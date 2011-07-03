{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
module Chord where

-- | TODO
-- When a node never responds, it should be removed from the fingertable, maybe actively replaced?
--
-- When a node joins, it very often get it self as it's successor, that's _never_ correct for joins, only lookups to keys, think this has been fixed
--
-- When a node joins, it makes 160 _sequenced_ lookups, these are to discover what nodes are on the net.
-- If the lookup times out, it's going to take 160*timeout for it to complete and leave 160 "Timeout" messages
-- in the logs
--

-- {{{ imports
import Remote.Call
import Remote.Channel
import Remote.Peer
import Remote.Process
import Remote.Init
import Remote.Encoding
import Remote.Reg
import Remote

import Control.Monad (liftM)
import Data.Typeable
import Control.Monad.IO.Class (liftIO)

import Control.Concurrent (threadDelay)
import Control.Concurrent.MVar
import qualified Control.Exception as Ex

import qualified Data.Map as Map
import Data.List (foldl')

import Data.Digest.Pure.SHA
import Data.Binary
import qualified Data.ByteString.Char8 as BS

import IO
-- }}}

-- for helper debug
import qualified Data.List as List
import System.Random (randomRIO)
import Data.Ratio
import Maybe (fromJust)

--{{{ Data type and type class definitions

-- | The successor list is from the closest to the farther away
data FingerEntry = SuccessorList [NodeId] | FingerNode NodeId deriving (Eq, Show, Typeable)

instance Binary FingerEntry where
  put (SuccessorList ns) = do put (0 :: Word8)
                              put ns
  put (FingerNode n) = do put (1 :: Word8)
                          put n
  get = do flag <- getWord8
           case flag of
             0 -> get >>= (return . SuccessorList)
             1 -> get >>= (return . FingerNode)

type FingerTable = Map.Map Integer FingerEntry

-- | NodeState, carries all important state variables
data NodeState = NodeState {
          self :: NodeId
        , fingerTable :: FingerTable -- ^ The fingerTable
        , blockDir :: FilePath -- ^ The dir to store the blocks
        , predecessor :: NodeId
        , timeout :: Int -- ^ The timout latency of ping
        , m :: Integer -- ^ The number of bits in a key, ususaly 160
        , r :: Integer -- ^ The number of replicated blocks and nodes in the successor list
        } deriving (Show)

instance Binary NodeState where
  put a = do put (self a)
             put (fingerTable a)
             put (blockDir a)
	     put (predecessor a)
	     put (timeout a)
	     put (m a)
             put (r a)
  get = do se <- get
           ft <- get
           bd <- get
	   pr <- get
	   ti <- get
	   m <- get
           r <- get
	   return (NodeState { self = se, fingerTable = ft, blockDir = bd, predecessor = pr, timeout = ti, m=m, r=r })

successor :: NodeState -> Maybe NodeId
successor st
  | (liftM length (successors st)) == (Just 0) = Nothing --error "No successors"
  | otherwise = liftM head $ successors st

successors :: NodeState -> Maybe [NodeId]
successors st
  | Just (SuccessorList ns) <- Map.lookup 1 (fingerTable st)
  , length ns /= 0 -- We can't give an empty list back
  = Just ns
  | otherwise = Nothing

cNodeId :: NodeId -> Integer
cNodeId n = integerDigest . sha1 $ encode n

data FingerResults = Has [NodeId] | HasNot | Empty
--}}}

-- {{{ algorithmic stuff
-- {{{ hasSuccessor
-- | Shuld return the successor of US if the key asked for is in the domain (us, successor]
hasSuccessor :: NodeState -> Integer -> FingerResults
hasSuccessor st key
  | Just False <- liftM List.null (successors st) = do
   let n = cNodeId (self st)
       maySuccs = successors st
   case maySuccs of
     Nothing -> HasNot
     (Just succs) -> if between key n ((cNodeId . head $ succs) + 1)
                    then Has succs
                    else HasNot
  | otherwise = Empty
-- }}}

-- {{{ closestPrecedingNode
closestPreceding :: NodeState -> Integer -> [NodeId]
closestPreceding st key = closestPreceding' st (fingerTable st) key (m st) []

closestPreceding' :: NodeState -> FingerTable -> Integer -> Integer -> [NodeId] -> [NodeId]
closestPreceding' st fingers key 0 ns
  | length ns >= fromInteger (r st) = ns
  | otherwise = (self st):ns
closestPreceding' st fingers key i ns
  | length ns >= fromInteger (r st) = ns

  | (Just (SuccessorList hits)) <- lookopAndIf i fingers isBetween
  , length ns < fromInteger (r st)
  , (length ns) + (length hits) > fromInteger (r st)
  = closestPreceding' st fingers key (i-1) (nub ((take ((fromInteger (r st)) - (length ns)) hits)++ns))-- we have to add a part of the successor list

  | (Just (SuccessorList hits)) <- lookopAndIf i fingers isBetween
  , length ns < fromInteger (r st) -- We need more
  , (length ns) + (length hits) > fromInteger (r st) -- 
  = closestPreceding' st fingers key (i-1) (nub (hits++ns))-- we take the whole succesor list

  | (Just (FingerNode hit)) <- lookopAndIf i fingers isBetween
  , length ns < fromInteger (r st)
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
-- }}}

-- {{{ between
-- | is n in the domain of (a, b) ?
between :: Integer -> Integer -> Integer -> Bool
between n a b
  | a == b = n /= a --error "n can't be between a and b when a == b" -- can't be alike
  | (a < b) = (a < n) && (n < b)
  | (b < a) = not $ between n (b-1) (a+1)
-- }}}

-- {{{ addFinger
-- | Adds a finger to the fingertable. If there already exists a finger they are compared to see who's the best fit.
addFinger :: NodeId -> NodeState -> NodeState
addFinger newFinger st 
  | newFinger == (self st) = st
  | otherwise = st {fingerTable = foldl' pred (fingerTable st) [1..(m st)]}
    where pred :: FingerTable -> Integer -> FingerTable
          pred ft 1
            | Just (SuccessorList ns) <- Map.lookup 1 ft
            = Map.insert 1 (addToSuccessorList st newFinger [] ns) ft
            | otherwise = Map.insert 1 (addToSuccessorList st newFinger [] []) ft

          pred ft i
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
addToSuccessorList st node prev [] = SuccessorList . (take (fromInteger (r st))) . nub $ (prev ++ [node])
  where nub = (map head) . List.group
addToSuccessorList st node prev (cur:next)
  | between (cNodeId node) (cNodeId . self $ st) (cNodeId cur) = SuccessorList $ prev ++ [node] ++ (take ((fromInteger (r st)) - (length prev + 1)) next)
  | otherwise = addToSuccessorList st node (prev ++ [cur]) next

addFingers :: [NodeId] -> NodeState -> NodeState
addFingers ns st = List.foldl' (\st n -> addFinger n st) st ns

fingerVal ::  (Integral a) => NodeState -> a -> Integer
fingerVal st k = mod ((cNodeId . self $ st) + 2^(k-1)) (2^(m st))
-- }}}

-- {{{ removeFinger
removeFinger :: NodeId -> NodeState -> NodeState
removeFinger node st
  | node == (self st) = st
  | otherwise = remSuccList $ st { fingerTable = Map.filter (/= FingerNode node) (fingerTable st) }
  where remSuccList :: NodeState -> NodeState
        remSuccList st'
          | Just (SuccessorList ns) <- Map.lookup 1 (fingerTable st')
          = st' { fingerTable = Map.insert 1 (SuccessorList (List.filter (/= node) ns)) (fingerTable st') }
          | otherwise = st'
-- }}}
-- }}}

-- {{{ State stuff
data PassState = ReadState ProcessId
               | RetReadState NodeState
               | TakeState ProcessId
               | RetTakeState NodeState
               | PutState NodeState deriving (Show, Typeable)

instance Binary PassState where
  put (ReadState pid) = do put (0 :: Word8)
                           put pid
  put (RetReadState i) = do put (1 :: Word8)
                            put i

  put (TakeState pid) = do put (2 :: Word8)
                           put pid
  put (RetTakeState i) = do put (3 :: Word8)
                            put i
  put (PutState i) = do put (4 :: Word8)
                        put i
  get = do
        flag <- getWord8
        case flag of
          0 -> do
               pid <- get
               return (ReadState pid)
          1 -> do
               i <- get
               return (RetReadState i)
          2 -> do
               pid <- get
               return (TakeState pid)
          3 -> do
               i <- get
               return (RetTakeState i)
          4 -> do
               i <- get
               return (PutState i)

getState :: ProcessM NodeState
getState = do statePid <- getStatePid
              pid <- getSelfPid
              send statePid (ReadState pid)
              ret <- receiveTimeout 10000000 [ match (\(RetReadState st) -> return st) ]
              case ret of
                Nothing -> say "asked for state but state process did not return within timeout, retrying" >> getState
                Just st -> return st

modifyState :: (NodeState -> NodeState) -> ProcessM ()
modifyState f = do
                 statePid <- getStatePid
                 selfPid <- getSelfPid
                 send statePid (TakeState selfPid)
                 ret <- receiveTimeout 10000000 [ match (\(RetTakeState st) -> return st) ]
                 case ret of
                   Nothing -> say "asked for modify, timeout, ignoring and continuing" >> return ()
                   Just st -> send statePid (PutState (f st))

getStatePid :: ProcessM ProcessId
getStatePid = do nid <- getSelfNode
                 statePid <- nameQuery nid "CHORD-NODE-STATE"
                 case statePid of
                   Nothing -> say "State not initialized, state-process is not running" >> getStatePid
                   Just pid -> return pid
-- }}}

-- {{{ relayFndSucc
-- | someone asks you for a successor, if you know it you reply to the original caller,
-- | else you relay the query forward
relayFndSucc :: NodeId -> ProcessId -> Integer -> ProcessM ()
relayFndSucc nid caller key = do
  modifyState (\x -> addFinger (nodeFromPid caller) (addFinger nid x))
  st <- getState
  let x = 2^(m st) :: Integer
      fm :: Integer -> Double
      fm = fromRational . (% x)
      sh :: Integer -> String
      sh = (take 5) . show
  case (hasSuccessor st key) of
      (Has suc) -> do 
             send caller suc -- we have the successor of the node
      HasNot -> do
          let recv = last $ closestPreceding st key -- | find the next to relay to
          case recv == (self st) of
            False -> do
              let clos = $( mkClosureRec 'relayFndSucc )
              flag <- ptry $ spawn recv (clos (self st) caller key) :: ProcessM (Either TransmitException ProcessId)
              case flag of
                Left _ -> modifyState (removeFinger recv) >> relayFndSucc nid caller key -- spawning failed
	        Right _ -> return ()
            True -> do
              say "THIS IS WRONG!" -- this should never happen because we should not be in the fingertable
              send caller (self st)
      Empty -> do
             send caller (self st)

getPred = do st <- getState
             return (predecessor st)
-- }}}

-- {{{ notify
-- | notifier is telling you he thinks he is your predecessor, check if it's true.
notify notifier = do
  st <- getState
  if between (cNodeId notifier) (cNodeId . predecessor $ st) (cNodeId . self $ st)
    then say "New predecessor" >> modifyState (\x -> x {predecessor = notifier})
    else return ()
-- }}}

-- {{{ ping
ping pid = send pid pid
-- }}}

$( remotable ['relayFndSucc, 'getPred, 'notify, 'ping] )

-- {{{ joinChord
-- | Joins a chord ring. Takes the id of a known node to bootstrap from.
joinChord :: NodeId -> ProcessM ()
joinChord node = do
    modifyState (addFinger node)
    st <- getState
    say $ "Join on: " ++ (show node)
    succ <- liftM (head . fromJust) $ remoteFindSuccessor node (mod ((cNodeId . self $ st) + 1) (m $ st))
    say $ "Ret self?: " ++ (show (succ == (self st))) ++ " Ret boot?: " ++ (show (succ == node))
    buildFingers succ
    sst <- getState
    --say $ "Finish join: " ++ (show . nils . fingerTable $ sst)
    let suc = successor sst
    case suc of
      (Just c) -> do ptry (spawn c (notify__closure (self st))) :: ProcessM (Either TransmitException ProcessId)
                     return ()
      Nothing -> say "joining got us no successor!" >> return ()
-- }}}

-- this is a debug function with a bogus name
--nils :: Map.Map Integer NodeId -> [NodeId]
--nils = (List.map (\x -> head x)) . List.group . List.sort . Map.elems -- TODO this is a debug function

-- {{{ checkAlive
checkAlive node = do pid <- getSelfPid
                     flag <- ptry $ spawn node (ping__closure pid) :: ProcessM (Either TransmitException ProcessId)
                     case flag of
                       Left _ -> say "dropped node" >> modifyState (removeFinger node) >> return False
                       Right _ -> do resp <- receiveTimeout 10000000 [match (\x -> return x)] :: ProcessM (Maybe ProcessId)
                                     case resp of
                                       Nothing -> do modifyState (removeFinger node)
                                                     say "dropped node"
                                                     return False
                                       Just pid -> return True
-- }}}

-- | Extracts all the nodes known to us from our state
-- {{{ fingerNodes
fingerNodes :: NodeState -> [NodeId]
fingerNodes st
  | Just (SuccessorList sl) <- Map.lookup 1 (fingerTable st)
  , fs <- (drop 1) . Map.elems $ (fingerTable st) :: [FingerEntry]
  = nub $ sl ++ (map strip fs)
  where nub = (map head) . List.group
        strip (FingerNode n) = n
-- }}}

-- {{{ checkFingerTable
checkFingerTable :: ProcessM ()
checkFingerTable = do st <- getState
                      sequence $ List.map checkAlive (fingerNodes st)
                      return ()
-- }}}

-- {{{ checkPred
checkPred :: ProcessM Bool
checkPred = do st <- getState
               flag <- checkAlive (predecessor st)
               if flag
                 then return True
                 else modifyState (\x -> x { predecessor = (self x) }) >> return False
-- }}}

-- {{{ stabilize
-- | This is run periodically to check if our fingertable is correct
stabilize = do
  liftIO $ threadDelay 5000000 -- 5 sec
  checkPred 
  checkFingerTable
  st <- getState
  case successor st of
    (Just succ) -> do alive <- checkAlive succ
                      if alive
                        then do succPred <- callRemote succ getPred__closure
                                if between (cNodeId succPred) (cNodeId . self $ st) (cNodeId succ)
                                  then do modifyState (addFinger succPred)
                                          st' <- getState
                                          ptry $ spawn succ (notify__closure (self st')) :: ProcessM (Either TransmitException ProcessId)
                                          say ("New succ: " ++ (show succPred)) >> stabilize
                                  else do ptry (spawn succ (notify__closure (self st))) :: ProcessM (Either TransmitException ProcessId)
                                          stabilize
                         else do say "Successor is dead, restabilizing"
                                 st' <- getState
                                 say (show . length . Map.elems . fingerTable $ st')
                                 findSuccessor $ mod ((cNodeId . self $ st) + 1) (2^(m st))
                                 stabilize
    Nothing -> stabilize
-- }}}

-- {{{ findSuccessor
-- | YOU are wordering who's the successor of a certain key, if you don't know yourself
-- | you relay it forward with YOU as the original caller.
findSuccessor :: Integer -> ProcessM [NodeId]
findSuccessor key = do
  st <- getState
  case (hasSuccessor st key) of
      (Has suc) -> return suc
      Empty -> return [self st]
      HasNot -> do
          selfPid <- getSelfPid -- ^ get your pid
          let recv = last $ closestPreceding st key -- | find the next to relay to
          case recv == (self st) of
            False -> do ret <- remoteFindSuccessor recv key
                        case ret of 
                          Nothing -> modifyState (removeFinger recv) >> findSuccessor key
                          Just succ -> return succ
            True -> say "THIS IS WRONG, we should not be in our own fingertable! retrying" >> liftIO (threadDelay 5000000) >> findSuccessor key
-- }}}

-- {{{ remoteFindSuccessor
remoteFindSuccessor :: NodeId -> Integer -> ProcessM (Maybe [NodeId])
remoteFindSuccessor node key = remoteFindSuccessor' node key 2
remoteFindSuccessor' _ _ 0 = return Nothing
remoteFindSuccessor' node key tries = do
  st <- getState
  selfPid <- getSelfPid
  ptry $ spawn node (relayFndSucc__closure (self st) selfPid (key :: Integer)) :: ProcessM (Either TransmitException ProcessId)
  succ <- receiveTimeout 10000000 [match (\x -> return x)] :: ProcessM (Maybe [NodeId])
  case succ of
    Nothing -> say "RemFndSucc timed out, retrying" >> remoteFindSuccessor' node (key :: Integer) (tries - 1)
    Just conts -> do
                modifyState (addFingers conts)
                return (Just conts)
-- }}}

-- {{{ buildFingers
buildFingers :: NodeId -> ProcessM ()
buildFingers buildNode = do
                      say $ "buildNode is: " ++ (show buildNode)
                      st <- getState
                      nodeId <- getSelfNode
                      let f i = remoteFindSuccessor buildNode i
                          nodids = map (fingerVal st) r
                          r = [1 .. (m $ st)]
                      fingers <- sequence $ map f nodids
                      return ()
-- }}}

-- {{{ bootStrap
bootStrap st _ = do
  selfN <- getSelfNode
  let st' = st { self = selfN, predecessor = selfN }
  peers <- getPeers
  let peers' = filter (/= selfN) $ findPeerByRole peers "NODE" -- remove ourselves from peerlist
  case length peers' >= 1 of
    True -> do
             spawnLocal $ handleState st'
             spawnLocal (joinChord (head peers'))
             spawnLocal stabilize
             
    False -> do spawnLocal $ handleState (addFinger (self st') st')
                spawnLocal stabilize
-- }}}

-- {{{ handleState
-- | handlet get and puts for the state
-- this function is butt ugly and needs some hefty sugar
handleState st' = do
  nameSet "CHORD-NODE-STATE"
  loop st'

  where loop :: NodeState -> ProcessM ()
        loop st = do
            receiveWait
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
                                                           _ -> False)  (\(PutState st) -> return st) ]
          case ret of
            Nothing -> say "process asked for modify, but did not return new state" >> return st
            Just newSt -> return newSt
-- }}}

