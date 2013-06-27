{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable,ScopedTypeVariables,DeriveGeneric #-}
module Control.Distributed.Process.DHT.Chord (
                        -- * Types
                        NodeId,
                        NodeState(..),
                        FingerTable,
                        -- * Initialization
                        bootstrap,
                        -- * Lookup
                        findSuccessors,
                        successors,
                        successor,
                        -- * State
                        getState,
                        -- * Utility
                        between, cNodeId,defaultInitState,
                        -- * Cloud haskell specific
                        __remoteTable, __remoteTableDecl
                        ) where

import Data.Binary
import Data.Digest.Pure.SHA
import Data.Int (Int64)
import qualified Data.Map as Map
import Data.Maybe (fromJust,isJust)
import qualified Data.List as List
import Data.Typeable
import GHC.Generics
import Control.Concurrent (threadDelay)
import Control.Concurrent.MVar
import Control.Monad (liftM,void,when,forever)

import Control.Distributed.Process
import Control.Distributed.Process.Closure
import Control.Distributed.Process.Node
import Control.Distributed.Backend.P2P hiding (bootstrap)

-- | The successor list is from the closest to the farther away
data FingerEntry = SuccessorList [NodeId] | FingerNode NodeId deriving (Eq, Show, Typeable,Generic)
instance Binary FingerEntry

type FingerTable = Map.Map Integer FingerEntry

-- | NodeState, carries all important state for a Chord DHT to function
data NodeState = NodeState {
          self :: NodeId
        , fingerTable :: FingerTable -- ^ The fingerTable
        , blockDir :: FilePath -- ^ The dir to store the blocks, not currently used since everything is stored in a HashTable in memory
        , predecessor :: NodeId -- ^ The node directly before us in the ring
        , timeout :: Int -- ^ The timout latency of ping
        , m :: Integer -- ^ The number of bits in a key, ususaly 160
        , r :: Int -- ^ The number of in the successor list, eg. 16
        , b :: Int -- ^ The number of replicas of each block, (b <= r)
        , blockSize :: Int64 -- ^ The number of bytes each block fills
        } deriving (Show,Typeable,Generic)
instance Binary NodeState

-- | 'successor' takes the state and tells us who our imidiate
-- successor is.
successor :: NodeState -> Maybe NodeId
successor st
  | null (successors st) = Nothing --error "No successors"
  | otherwise = Just . head . successors $ st

-- | 'successors' takes the state and tells us who
-- our 'r' imidiate successors are in rising order.
-- That is, node number 1 is the closest and node n
-- is the successor farthes away.
successors :: NodeState -> [NodeId]
successors st
  | Just (SuccessorList ns) <- Map.lookup 1 (fingerTable st)
  , not (null ns) -- We can't give an empty list back
  = ns
  | otherwise = []

-- | 'cNodeId' takes a 'NodeId' and return the SHA1 hash
-- of it. This is the ID/key of the NodeId.
cNodeId :: NodeId -> Integer
cNodeId n = integerDigest . sha1 $ encode n

data FingerResults = Has [NodeId] | HasNot | Empty

-- | 'hasSuccessor' tells us if we have the successors of a given key.
hasSuccessor :: NodeState -> Integer -> Int -> FingerResults
hasSuccessor st key howMany
  | List.null ss = Empty
  | between key (cNodeId (self st)) (cNodeId (head ss) + 1)
  = Has ss
  | otherwise = hasSuccessor' st key howMany (tail ss)
  where ss = successors st


-- | If we have enough successors in our list we return them if they
-- are successors of the key
hasSuccessor' :: NodeState -> Integer -> Int -> [NodeId] -> FingerResults
hasSuccessor' _ _ _ [] = HasNot
hasSuccessor' st key howMany succN@(s:ss)
  | length succN < howMany = HasNot
  | between key (cNodeId (self st)) ((cNodeId s) + 1) = Has succN
  | otherwise = hasSuccessor' st key howMany ss

-- | 'closestPreceding' is the node that has the 'NodeId' closest to the given key,
-- /but/ not above it that we know of in our 'NodeState'.
closestPreceding :: NodeState -> Integer -> [NodeId]
closestPreceding st key = closestPreceding' st (fingerTable st) key (m st) []

closestPreceding' :: NodeState -> FingerTable -> Integer -> Integer -> [NodeId] -> [NodeId]
closestPreceding' st _fingers _key 0 ns
  | length ns >= (r st) = ns
  | otherwise = (self st):ns
closestPreceding' st fingers key i ns
  | length ns >= (r st) = ns

  | (Just (SuccessorList hits)) <- lookopAndIf i fingers isBetween
  , length ns < (r st)
  , (length ns) + (length hits) > (r st)
  = closestPreceding' st fingers key (i-1) (nub ((take ((r st) - (length ns)) hits)++ns))-- we have to add a part of the successor list

  | (Just (SuccessorList hits)) <- lookopAndIf i fingers isBetween
  , length ns < r st -- We need more
  , (length ns) + (length hits) > r st
  = closestPreceding' st fingers key (i-1) (nub (hits++ns))-- we take the whole succesor list

  | (Just (FingerNode hit)) <- lookopAndIf i fingers isBetween
  , length ns < r st
  = closestPreceding' st fingers key (i-1) (nub (hit:ns))

  | otherwise = closestPreceding' st fingers key (i-1) ns
    where isBetween (FingerNode x) = between (cNodeId x) (cNodeId . self $ st) key -- isBetween is from the fingertable
          isBetween (SuccessorList []) = False
          isBetween (SuccessorList x) = between (cNodeId . head $ x) (cNodeId . self $ st) key -- isBetween is from the fingertable
          nub = (map head) . List.group


-- | Lookup a value, if a predicate on it is true, return it, else Nothing
lookopAndIf k m f
  | (Just a) <- Map.lookup k m
  , f a = Just a -- a is the node from the fingertable
  | otherwise = Nothing

-- | Is n in the domain of (a, b) ?
--
--
-- NB: This domain is closed. It's the same as
-- a < n < b just it's circular as Chords keyspace.
between :: Integer -> Integer -> Integer -> Bool
between n a b
  | a == b = n /= a --error "n can't be between a and b when a == b" -- can't be alike
  | (a < b) = (a < n) && (n < b)
  | (b < a) = not $ between n (b-1) (a+1)
-- }}}

-- | Adds a finger to the fingertable. If there already exists a
-- finger they are compared to see who's the best fit.
addFinger :: NodeId -> NodeState -> NodeState
addFinger newFinger st
  | newFinger == (self st) = st
  | otherwise = st {fingerTable = List.foldl' predN (fingerTable st) [1..(m st)]}
    where predN :: FingerTable -> Integer -> FingerTable
          predN ft 1
            | Just (SuccessorList ns) <- Map.lookup 1 ft
            = Map.insert 1 (addToSuccessorList st newFinger [] ns) ft
            | otherwise = Map.insert 1 (addToSuccessorList st newFinger [] []) ft

          predN ft i
            | Just (FingerNode prevFinger) <- Map.lookup i ft -- there exists a node in the fingertable, is the new one closer?
            , let fv = fingerVal st i in (between c fv (cNodeId prevFinger)) && (between c fv n)
            = Map.insert i (FingerNode newFinger) ft

            | Nothing <- Map.lookup i ft -- there is no node, we just put it in if it fits
            , let fv = fingerVal st i in (between c fv n)
            = Map.insert i (FingerNode newFinger) ft
            | otherwise = ft

          c = cNodeId newFinger
          n = cNodeId (self st)

addToSuccessorList :: NodeState -> NodeId -> [NodeId] -> [NodeId] -> FingerEntry
addToSuccessorList st node prev [] = SuccessorList . (take (r st)) . nub $ (prev ++ [node])
  where nub = (map head) . List.group
addToSuccessorList st node prev (cur:next)
  | between (cNodeId node) (cNodeId . self $ st) (cNodeId cur) = SuccessorList . (take (r st)) . nub $ prev ++ [node] ++ next
  | otherwise = addToSuccessorList st node (prev ++ [cur]) next
  where nub = (map head) . List.group

addFingers :: [NodeId] -> NodeState -> NodeState
addFingers ns st = List.foldl' (flip addFinger) st ns

fingerVal ::  (Integral a) => NodeState -> a -> Integer
fingerVal st k = mod ((cNodeId . self $ st) + 2^(k-1)) (2^(m st))

-- | Ttakes a 'NodeId' and a 'NodeState' and removes all
-- occurences of it in the 'NodeState'. This is used when a node
-- leaves or times out.
removeFinger :: NodeId -> NodeState -> NodeState
removeFinger node st
  | node == (self st) = st
  | otherwise = remSuccList $ st { fingerTable = Map.filter (/= FingerNode node) (fingerTable st) }
  where remSuccList :: NodeState -> NodeState
        remSuccList st'
          | Just (SuccessorList ns) <- Map.lookup 1 (fingerTable st')
          = st' { fingerTable = Map.insert 1 (SuccessorList (List.filter (/= node) ns)) (fingerTable st') }
          | otherwise = st'

-- | 'PassState' let's us pass state around between the
-- 'handleState' process and all the others.
data PassState = ReadState ProcessId
               | RetReadState NodeState
               | TakeState ProcessId
               | RetTakeState NodeState
               | PutState NodeState deriving (Show,Typeable,Generic)
instance Binary PassState

-- | 'getState' lets us retrive the current state from the
-- 'handleState' process.
getState :: Process NodeState
getState = do statePid <- getStatePid
              pid <- getSelfPid
              send statePid (ReadState pid)
              ret <- receiveTimeout 10000000 [ match (\(RetReadState st) -> return st) ]
              case ret of
                Nothing -> say "asked for state but state process did not return within timeout, retrying" >> getState
                Just st -> return st

-- | 'modifyState' takes a 'NodeState'-modifying function and
-- runs it on the current state updating it.
modifyState :: (NodeState -> NodeState) -> Process NodeState
modifyState f = do
                 statePid <- getStatePid
                 selfPid <- getSelfPid
                 send statePid (TakeState selfPid)
                 ret <- receiveTimeout 10000000 [ match (\(RetTakeState st) -> return st) ]
                 case ret of
                   Nothing -> say "asked for modify, timeout, retrying" >> liftIO (threadDelay 50000000) >> modifyState f
                   Just st -> send statePid (PutState (f st)) >> return (f st)

-- | 'getStatePid' gives us the 'ProcessId' of the 'handleState' process.
getStatePid :: Process ProcessId
getStatePid = do nid <- getSelfNode
                 -- statePid <- nameQuery nid "CHORD-NODE-STATE"
                 whereisRemoteAsync nid "CHORD-NODE-STATE"
                 (WhereIsReply _str statePid) <- expect
                 case statePid of
                   Nothing -> say "State not initialized, state-process is not running" >> getStatePid
                   Just pid -> return pid

getPred :: Process NodeId
getPred = do st <- getState
             return (predecessor st)

-- | notifier is telling you he thinks he is your predecessor, check if it's true.
-- and update the 'NodeState' accordingly.
notify :: NodeId -> Process ()
notify notifier = do
  st <- getState
  when (between (cNodeId notifier) (cNodeId . predecessor $ st) (cNodeId . self $ st)) $ do
    say "New predecessor"
    void $ modifyState (\x -> x {predecessor = notifier})

ping :: ProcessId -> Process ()
ping pid = send pid pid

-- | debug function, makes a remote node say a string.
remoteSay :: String -> Process ()
remoteSay = say

sdictNodeId :: SerializableDict NodeId
sdictNodeId = SerializableDict

remotable [ 'getPred , 'sdictNodeId , 'notify , 'ping , 'remoteSay , 'getState ]

-- | internal function: 'relayFndSucc' is called when a node does not know
-- the answer to a 'findSuccessors' call. For each call, we halve
-- the distance to the answer.
remotableDecl [
    [d| relayFndSucc :: (NodeId,ProcessId,Integer,Int) -> Process () ;
        relayFndSucc (nid,caller,key,howMany) = do
          void $ modifyState (addFinger (processNodeId caller) . addFinger nid)
          st <- getState
          case (hasSuccessor st key howMany) of
              (Has suc) -> send caller suc -- we have the successor of the node
              HasNot -> do
                  let recv = last $ closestPreceding st key -- find the next to relay to
                  if (recv == (self st))
                    then do
                      say "THIS IS WRONG!" -- this should never happen because we should not be in the fingertable
                      send caller (self st)
                    else do
                      -- let clos = $( mkClosure 'relayFndSucc )
                      void $ spawn recv ($(mkClosure 'relayFndSucc) ((self st),caller,key,howMany))
                      {- TODO
                      flag <- try $ spawn recv (clos (self st) caller key howMany) :: Process (Either TransmitException ProcessId)
                      case flag of
                        Left _ -> say "could not spawn" >> modifyState (removeFinger recv) >> relayFndSucc nid caller key howMany -- spawning failed
                        Right _ -> return ()
                      -}
              Empty -> send caller (self st)
      |]
  ]

-- | Joins a chord ring. Takes the id of a known node to bootstrap from.
-- This is not the function you would use to start a Chord Node, for that
-- use 'bootstrap'.
joinChord :: NodeId -> Process ()
joinChord node = do
    st <- modifyState (addFinger node)
    say $ "Join on: " ++ (show node)
    succN <- liftM (head . fromJust) $ remoteFindSuccessor node (mod ((cNodeId . self $ st) + 1) (m $ st)) (r st)
    say $ "Ret self?: " ++ (show (succN == (self st))) ++ " Ret boot?: " ++ (show (succN == node))
    buildFingers succN
    sst <- getState
    --say $ "Finish join: " ++ (show . nils . fingerTable $ sst)
    let suc = successor sst
    case suc of
      (Just c) -> do (void $ spawn c ($(mkClosure 'notify) (self st))) -- :: Process (Either TransmitException ProcessId)
                     return ()
      Nothing -> void $ say "joining got us no successor!"

-- | 'checkAlive' checks if a single node is alive, if it's
-- not we'll discard it from our 'fingerTable'.
checkAlive :: NodeId -> Process Bool
checkAlive node = do
    mv <- liftIO newEmptyMVar
    catchExit
      (void $ spawnLocal $ do
        whereisRemoteAsync node "ping-server"
        reply <- expectTimeout 10000000
        case reply of
          Just (WhereIsReply _str maybePid) -> liftIO (putMVar mv (isJust maybePid))
          Nothing -> liftIO (putMVar mv False))
      (\_from (_reason::String) -> liftIO (putMVar mv False))
    liftIO $ takeMVar mv

-- | Utility function that takes a 'NodeState' and
-- returns all the 'NodeId's that we know
fingerNodes :: NodeState -> [NodeId]
fingerNodes st
  | Just (SuccessorList sl) <- Map.lookup 1 (fingerTable st)
  , fs <- (drop 1) . Map.elems $ (fingerTable st) :: [FingerEntry]
  = nub $ sl ++ (map strip fs)
  | otherwise = []
  where nub = (map head) . List.group
        strip (FingerNode n) = n

-- TODO: does it? checkAlive simply  returns a Bool, and
--       checkFingerTable doesn't do anything.
-- | 'checkFingerTable' checks if the nodes in our 'fingerTable' is alive
-- and discards them if they're not
checkFingerTable :: Process ()
checkFingerTable = do st <- getState
                      mapM_ checkAlive (fingerNodes st)

-- | 'checkPred' checks if our 'predecessor' is alive.
checkPred :: Process Bool
checkPred = do st <- getState
               flag <- checkAlive (predecessor st)
               if flag
                 then return True
                 else modifyState (\x -> x { predecessor = (self x) }) >> return False

-- | This is run periodically to check if our fingertable is correct
-- It is the one that handles node failures, leaves and joins.
-- It's an internal function
stabilize :: Process ()
stabilize = do
  liftIO $ threadDelay 5000000 -- 5 sec
  void checkPred
  checkFingerTable
  st <- getState
  case successor st of
    (Just succN) -> do
                      alive <- checkAlive succN
                      if alive
                        then do (succPred :: NodeId) <- call $(mkStatic 'sdictNodeId) succN $(mkStaticClosure 'getPred)
                                if between (cNodeId succPred) (cNodeId . self $ st) (cNodeId succN)
                                  then do void $ modifyState (addFinger succPred)
                                          void $ spawn succN ($(mkClosure 'notify) (self st)) -- :: Process (Either TransmitException ProcessId)
                                          say ("New succ: " ++ (show succPred)) >> stabilize
                                  else do (void $ spawn succN ($(mkClosure 'notify) (self st))) -- :: Process (Either TransmitException ProcessId)
                                          stabilize
                         else do say "Successor is dead, restabilizing"
                                 void $ findSuccessors (mod ((cNodeId . self $ st) + 1) (2^(m st))) (r st)
                                 stabilize
    Nothing -> stabilize

-- | This is the main function of the Chord DHT. It lets you lookup
-- what 'NodeId's has the responsebility for the given key
findSuccessors :: Integer -> Int -> Process [NodeId]
findSuccessors key howMany = do
  st <- getState
  case (hasSuccessor st key howMany) of
      (Has suc) -> return suc
      Empty -> return [self st]
      HasNot -> do
          -- selfPid <- getSelfPid
          let recv = last $ closestPreceding st key
          if recv == (self st)
            then do
              say "THIS IS WRONG, we should not be in our own fingertable! retrying"
              liftIO (threadDelay 5000000)
              findSuccessors key howMany
            else do
              ret <- remoteFindSuccessor recv key howMany
              case ret of
                Nothing -> modifyState (removeFinger recv) >>
                           findSuccessors key howMany
                Just succN -> return succN


-- | 'remoteFindSuccessor' takes a 'NodeId' the key to lookup and a number of how
-- many successors to get.
remoteFindSuccessor :: NodeId -> Integer -> Int -> Process (Maybe [NodeId])
remoteFindSuccessor node key howMany = remoteFindSuccessor' node key howMany 2
remoteFindSuccessor' :: NodeId -> Integer -> Int -> Int -> Process (Maybe [NodeId])
remoteFindSuccessor' _ _ _ 0 = return Nothing
remoteFindSuccessor' node key howMany tries = do
  st <- getState
  selfPid <- getSelfPid
  void $ spawn node ($(mkClosure 'relayFndSucc) ((self st),selfPid,(key :: Integer),(howMany :: Int))) -- :: Process (Either TransmitException ProcessId)

  -- maybe it should be checked for errors in the try, if the error is local something will not work?
  succN <- receiveTimeout 10000000 [match return] :: Process (Maybe [NodeId])
  case succN of
    Nothing -> say "RemFndSucc timed out, retrying" >> remoteFindSuccessor' node (key :: Integer) (howMany :: Int) (tries - 1)
    Just conts -> do
                void $ modifyState (addFingers conts)
                return (Just conts)

-- |'buildFingers' takes a 'NodeId' and does a lookup
-- for sucessors to each index in our fingertable
buildFingers :: NodeId -> Process ()
buildFingers buildNode = do
                      say $ "buildNode is: " ++ (show buildNode)
                      st <- getState
                      -- nodeId <- getSelfNode
                      let f :: Integer -> Process (Maybe [NodeId])
                          f i = remoteFindSuccessor buildNode i (r st)
                          nodids = map (fingerVal st) nums
                          nums = [1 .. (m $ st)]
                      mapM_ f nodids

-- | Starts a Chord Node and joins the network trough a list of peers.
-- It takes the initial state, lookups other Chord-nodes
-- on the LAN, starts state handeling, stabilizing etc.
-- in the background and then runs 'joinChord' on the first
-- and best node that's altready a member in the ring.
bootstrap :: NodeState -> LocalNode -> [NodeId] -> Process ()
bootstrap st myNode peers = do
    let myNodeId = localNodeId myNode
    let st' = st { self = myNodeId , predecessor = myNodeId }
    let peers' = filter (/= myNodeId) peers -- $ findPeerByRole peers "NODE" -- remove ourselves from peerlist
    pingServer <- spawnLocal (forever (expect :: Process String)) -- (won't actually receive messages, just used to register pid)
    register "ping-server" pingServer
    void $
      if not (null peers')
       then do
         spawnLocal $ handleState st'
         spawnLocal (joinChord (head peers'))
         spawnLocal stabilize
       else do
         spawnLocal $ handleState (addFinger (self st') st')
         spawnLocal stabilize

-- | default settings for inital 'NodeState'
defaultInitState :: NodeState
defaultInitState = NodeState {
          self = undefined
        , fingerTable = Map.empty -- ^ The fingerTable
        , blockDir = "/tmp/"
        , predecessor = undefined
        , timeout = 10 -- ^ The timout latency of ping
        , m = 160 -- ^ The number of bits in a key, ususaly 160
        , r = 5 -- ^ the number of successors
        , b = 2 -- ^ the nuber of replicas
        , blockSize = 10 -- ^ the number of bytes a block is
        }

-- | This is an internal function, it handles gets and puts for the state
-- this function is butt ugly and needs some hefty sugar
handleState :: NodeState -> Process ()
handleState st' = do
    myPid <- getSelfPid
    register "CHORD-NODE-STATE" myPid
    loop st'
  where loop :: NodeState -> Process ()
        loop st = receiveWait
            [ matchIf (\x -> case x of
                (ReadState _) -> True
                _ -> False) (\(ReadState pid) -> getSt st pid)
            , matchIf (\x -> case x of
                (TakeState _) -> True
                _ -> False) (\(TakeState pid) -> modSt st pid) ]
            >>= loop
        getSt st pid = do
          send pid (RetReadState st)
          return st
        modSt st pid = do
          send pid (RetTakeState st)
          ret <- receiveTimeout 1000000 [ matchIf (\x -> case x of
                                                           (PutState _) -> True
                                                           _ -> False)  (\(PutState st') -> return st') ]
          case ret of
            Nothing -> say "process asked for modify, but did not return new state" >> return st
            Just newSt -> return newSt
