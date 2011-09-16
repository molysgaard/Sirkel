{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
module Remote.DHT.Chord (
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
                        between, cNodeId,
                        -- * Cloud haskell specific
                        __remoteCallMetaData
                        ) where

-- {{{ imports
import Remote
import Remote.Process
import Remote.Call

import Data.Typeable
import Data.Binary
import Data.Digest.Pure.SHA

import Control.Monad.IO.Class (liftIO)
import Control.Monad (liftM)
import Control.Concurrent (threadDelay)

import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.ByteString.Lazy.Char8 as BS

import Maybe (fromJust)
import Data.Int (Int64)
-- }}}

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
        } deriving (Show)

instance Binary NodeState where
  put a = do put (self a)
             put (fingerTable a)
             put (blockDir a)
             put (predecessor a)
             put (timeout a)
             put (m a)
             put (r a)
             put (b a)
             put (blockSize a)
  get = do se <- get
           ft <- get
           bd <- get
           pr <- get
           ti <- get
           m <- get
           r <- get
           b <- get
           blockSize <- get
           return (NodeState { self = se, fingerTable = ft, blockDir = bd, predecessor = pr, timeout = ti, m=m, r=r, b=b, blockSize=blockSize })

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
  , length ns /= 0 -- We can't give an empty list back
  = ns
  | otherwise = []

-- | 'cNodeId' takes a 'NodeId' and return the SHA1 hash
-- of it. This is the ID/key of the NodeId.
cNodeId :: NodeId -> Integer
cNodeId n = integerDigest . sha1 $ encode n

data FingerResults = Has [NodeId] | HasNot | Empty
--}}}

-- {{{ algorithmic stuff
-- {{{ hasSuccessor
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
hasSuccessor' _ _ _ [] = HasNot
hasSuccessor' st key howMany succ@(s:ss)
  | length succ < howMany = HasNot
  | between key (cNodeId (self st)) ((cNodeId s) + 1) = Has succ
  | otherwise = hasSuccessor' st key howMany ss
-- }}}

-- {{{ closestPrecedingNode
-- | 'closestPreceding' is the node that has the 'NodeId' closest to the given key,
-- /but/ not above it that we know of in our 'NodeState'.
closestPreceding :: NodeState -> Integer -> [NodeId]
closestPreceding st key = closestPreceding' st (fingerTable st) key (m st) []

closestPreceding' :: NodeState -> FingerTable -> Integer -> Integer -> [NodeId] -> [NodeId]
closestPreceding' st fingers key 0 ns
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
-- }}}

-- {{{ between
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

-- {{{ addFinger
-- | Adds a finger to the fingertable. If there already exists a
-- finger they are compared to see who's the best fit.
addFinger :: NodeId -> NodeState -> NodeState
addFinger newFinger st 
  | newFinger == (self st) = st
  | otherwise = st {fingerTable = List.foldl' pred (fingerTable st) [1..(m st)]}
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
addToSuccessorList st node prev [] = SuccessorList . (take (r st)) . nub $ (prev ++ [node])
  where nub = (map head) . List.group
addToSuccessorList st node prev (cur:next)
  | between (cNodeId node) (cNodeId . self $ st) (cNodeId cur) = SuccessorList . (take (r st)) . nub $ prev ++ [node] ++ next
  | otherwise = addToSuccessorList st node (prev ++ [cur]) next
  where nub = (map head) . List.group

addFingers :: [NodeId] -> NodeState -> NodeState
addFingers ns st = List.foldl' (\st n -> addFinger n st) st ns

fingerVal ::  (Integral a) => NodeState -> a -> Integer
fingerVal st k = mod ((cNodeId . self $ st) + 2^(k-1)) (2^(m st))
-- }}}

-- {{{ removeFinger
-- 'removeFinger' takes a 'NodeId' and a 'NodeState' and removes all
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
-- }}}
-- }}}

-- {{{ State stuff
-- | 'PassState' let's us pass state around between the
-- 'handleState' process and all the others.
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

-- | 'getState' lets us retrive the current state from the
-- 'handleState' process.
getState :: ProcessM NodeState
getState = do statePid <- getStatePid
              pid <- getSelfPid
              send statePid (ReadState pid)
              ret <- receiveTimeout 10000000 [ match (\(RetReadState st) -> return st) ]
              case ret of
                Nothing -> say "asked for state but state process did not return within timeout, retrying" >> getState
                Just st -> return st

-- | 'modifyState' takes a 'NodeState'-modifying function and
-- runs it on the current state updating it.
modifyState :: (NodeState -> NodeState) -> ProcessM NodeState
modifyState f = do
                 statePid <- getStatePid
                 selfPid <- getSelfPid
                 send statePid (TakeState selfPid)
                 ret <- receiveTimeout 10000000 [ match (\(RetTakeState st) -> return st) ]
                 case ret of
                   Nothing -> say "asked for modify, timeout, retrying" >> liftIO (threadDelay 50000000) >> modifyState f
                   Just st -> send statePid (PutState (f st)) >> return (f st)

-- | 'getStatePid' gives us the 'ProcessId' of the 'handleState' process.
getStatePid :: ProcessM ProcessId
getStatePid = do nid <- getSelfNode
                 statePid <- nameQuery nid "CHORD-NODE-STATE"
                 case statePid of
                   Nothing -> say "State not initialized, state-process is not running" >> getStatePid
                   Just pid -> return pid
-- }}}

-- {{{ relayFndSucc
-- | internal function: 'relayFndSucc' is called when a node does not know
-- the answer to a 'findSuccessors' call. For each call, we halve
-- the distance to the answer.
relayFndSucc :: NodeId -> ProcessId -> Integer -> Int -> ProcessM ()
relayFndSucc nid caller key howMany = do
  modifyState (\x -> addFinger (nodeFromPid caller) (addFinger nid x))
  st <- getState
  case (hasSuccessor st key howMany) of
      (Has suc) -> do 
             send caller suc -- we have the successor of the node
      HasNot -> do
          let recv = last $ closestPreceding st key -- find the next to relay to
          case recv == (self st) of
            False -> do
              let clos = $( mkClosureRec 'relayFndSucc )
              flag <- ptry $ spawn recv (clos (self st) caller key howMany) :: ProcessM (Either TransmitException ProcessId)
              case flag of
                Left _ -> say "could not spawn" >> modifyState (removeFinger recv) >> relayFndSucc nid caller key howMany -- spawning failed
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
-- and update the 'NodeState' accordingly.
notify :: NodeId -> ProcessM ()
notify notifier = do
  st <- getState
  if between (cNodeId notifier) (cNodeId . predecessor $ st) (cNodeId . self $ st)
    then say "New predecessor" >> modifyState (\x -> x {predecessor = notifier}) >> return ()
    else return ()
-- }}}

-- {{{ ping
ping pid = send pid pid
-- }}}

-- | debug function, makes a remote node say a string.
remoteSay str = say str

$( remotable ['relayFndSucc, 'getPred, 'notify, 'ping, 'remoteSay] )

-- {{{ joinChord
-- | Joins a chord ring. Takes the id of a known node to bootstrap from.
-- This is not the function you would use to start a Chord Node, for that
-- use 'bootstrap'.
joinChord :: NodeId -> ProcessM ()
joinChord node = do
    st <- modifyState (addFinger node)
    say $ "Join on: " ++ (show node)
    succ <- liftM (head . fromJust) $ remoteFindSuccessor node (mod ((cNodeId . self $ st) + 1) (m $ st)) (r st)
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

-- {{{ checkAlive
-- | 'checkAlive' checks if a single node is alive, if it's
-- not we'll discard it from our 'fingerTable'.
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

-- {{{ fingerNodes
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
-- }}}

-- {{{ checkFingerTable
-- | 'checkFingerTable' checks if the nodes in our 'fingerTable' is alive
-- and discards them if they're not
checkFingerTable :: ProcessM ()
checkFingerTable = do st <- getState
                      sequence $ List.map checkAlive (fingerNodes st)
                      return ()
-- }}}

-- {{{ checkPred
-- | 'checkPred' checks if our 'predecessor' is alive.
checkPred :: ProcessM Bool
checkPred = do st <- getState
               flag <- checkAlive (predecessor st)
               if flag
                 then return True
                 else modifyState (\x -> x { predecessor = (self x) }) >> return False
-- }}}

-- {{{ stabilize
-- | This is run periodically to check if our fingertable is correct
-- It is the one that handles node failures, leaves and joins.
-- It's an internal function
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
                                          ptry $ spawn succ (notify__closure (self st)) :: ProcessM (Either TransmitException ProcessId)
                                          say ("New succ: " ++ (show succPred)) >> stabilize
                                  else do ptry (spawn succ (notify__closure (self st))) :: ProcessM (Either TransmitException ProcessId)
                                          stabilize
                         else do say "Successor is dead, restabilizing"
                                 findSuccessors (mod ((cNodeId . self $ st) + 1) (2^(m st))) (r st)
                                 stabilize
    Nothing -> stabilize
-- }}}

-- {{{ findSuccessors
-- | This is the main function of the Chord DHT. It lets you lookup
-- what 'NodeId's has the responsebility for the given key
findSuccessors :: Integer -> Int -> ProcessM [NodeId]
findSuccessors key howMany = do
  st <- getState
  case (hasSuccessor st key howMany) of
      (Has suc) -> return suc
      Empty -> return [self st]
      HasNot -> do
          selfPid <- getSelfPid
          let recv = last $ closestPreceding st key
          case recv == (self st) of
            False -> do ret <- remoteFindSuccessor recv key howMany
                        case ret of 
                          Nothing -> modifyState (removeFinger recv) >> findSuccessors key howMany
                          Just succ -> return succ
            True -> say "THIS IS WRONG, we should not be in our own fingertable! retrying" >> liftIO (threadDelay 5000000) >> findSuccessors key howMany
-- }}}

-- {{{ remoteFindSuccessor
-- | 'remoteFindSuccessor' takes a 'NodeId' the key to lookup and a number of how
-- many successors to get.
remoteFindSuccessor :: NodeId -> Integer -> Int -> ProcessM (Maybe [NodeId])
remoteFindSuccessor node key howMany = remoteFindSuccessor' node key howMany 2
remoteFindSuccessor' :: NodeId -> Integer -> Int -> Int -> ProcessM (Maybe [NodeId])
remoteFindSuccessor' _ _ _ 0 = return Nothing
remoteFindSuccessor' node key howMany tries = do
  st <- getState
  selfPid <- getSelfPid
  ptry $ spawn node (relayFndSucc__closure (self st) selfPid (key :: Integer) (howMany :: Int)) :: ProcessM (Either TransmitException ProcessId)
  -- maybe it should be checked for errors in the ptry, if the error is local something will not work?
  succ <- receiveTimeout 10000000 [match (\x -> return x)] :: ProcessM (Maybe [NodeId])
  case succ of
    Nothing -> say "RemFndSucc timed out, retrying" >> remoteFindSuccessor' node (key :: Integer) (howMany :: Int) (tries - 1)
    Just conts -> do
                modifyState (addFingers conts)
                return (Just conts)
-- }}}

-- {{{ buildFingers
-- |'buildFingers' takes a 'NodeId' and does a lookup
-- for sucessors to each index in our fingertable
buildFingers :: NodeId -> ProcessM ()
buildFingers buildNode = do
                      say $ "buildNode is: " ++ (show buildNode)
                      st <- getState
                      nodeId <- getSelfNode
                      let f :: Integer -> ProcessM (Maybe [NodeId])
                          f i = remoteFindSuccessor buildNode i (r st)
                          nodids = map (fingerVal st) nums
                          nums = [1 .. (m $ st)]
                      mapM_ f nodids
-- }}}

-- {{{ bootstrap
-- | Starts a Chord Node. It takes the initial state,
-- lookups other Chord-nodes
-- on the LAN, starts state handeling, stabilizing etc.
-- in the background and then runs 'joinChord' on the first
-- and best node that's altready a member in the ring.
bootstrap st = do
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
-- | This is an internal function, it handles gets and puts for the state
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
