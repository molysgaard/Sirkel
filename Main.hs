{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
module Main where

import Remote.Call
import Remote.Channel
import Remote.Peer
import Remote.Process
import Remote.Init
import Remote.Encoding

import Data.Ratio
import Debug.Trace
import Control.Monad
import Prelude hiding (break)
import Data.List hiding (break)
import Data.IORef
import Data.Array.IO
import Data.Array
import Data.Typeable
import qualified Control.Monad.State as St

import Control.Concurrent
import Control.Concurrent.STM
import qualified Data.Map as Map

import Data.Digest.Pure.SHA
import Data.Binary

--{{{ Data type and type class definitions
-- | NodeState, carries all important state variables
data NodeState = NodeState {
          self :: NodeId
        , fingerTable :: Map.Map Integer NodeId -- ^ The fingerTable
        , predecessor :: NodeId
        , timeout :: Int -- ^ The timout latency of ping
        , m :: Int -- ^ The number of bits in a key, ususaly 160
        , alpha :: Int -- ^ The number of parralell queries
        } deriving (Show)
instance Eq NodeState where
    (==) st1 st2 = ((self st1) == (self st2)) && 
                   ((fingerTable st1) == (fingerTable st2)) &&
                   ((predecessor st1) == (predecessor st2))
    (/=) st1 st2 = not $ (==) st1 st2


instance Binary NodeState where
  put a = do put (self a)
             put (fingerTable a)
	     put (predecessor a)
	     put (timeout a)
	     put (m a)
	     put (alpha a)
  get = do se <- get
           ft <- get
	   pr <- get
	   ti <- get
	   m <- get
	   a <- get
	   return (NodeState { self = se, fingerTable = ft, predecessor = pr, timeout = ti, m=m, alpha=a })

successor :: NodeState -> Maybe NodeId
successor st = helper st 1
    where helper st k
            | fromIntegral k > (m st) = Nothing
            | Just c <- Map.lookup k (fingerTable st) = Just c
            | otherwise = helper st (k+1)

type Key = Integer

cNodeId n = integerDigest . sha1 $ encode n
--}}}

-- | Shuld return the successor of US if the key asked for is BETWEEN us and the successor
hasSuccessor :: NodeState -> Key -> Maybe NodeId
hasSuccessor st key = do
   let n = cNodeId (self st)
       suc = successor st
   case suc of
     Nothing -> Nothing
     (Just succ) -> if ((n < key) && (key <= (cNodeId succ)))
                    then Just succ
                    else Nothing

-- {{{ closestPrecedingNode
closestPreceding st key = do
  return $ helper st (fingerTable st) key (fromIntegral . m $ st)

helper :: (Ord k, Num k) => NodeState -> Map.Map k NodeId -> Key -> k -> NodeId
helper st conts key 0 = error "error in closest node"
helper st conts key n
  | (Just c) <- lookopAndIf c conts n = c
  | otherwise = helper st conts key (n-1)
    where c1 x = (cNodeId $ self st) < (cNodeId x)
          c2 x = (cNodeId x) <= key
          c x = True
          --c x = (c1 x) && (c2 x)


-- | Lookup a value, if a predicate on it is true, return it, else Nothing
lookopAndIf :: (Ord k) => (a -> Bool) -> Map.Map k a -> k -> Maybe a
lookopAndIf f m k
  | (Just a) <- Map.lookup k m
  , f a = Just a
  | otherwise = Nothing
-- }}}

-- {{{ addFinger
addFinger :: NodeId -> NodeState -> NodeState
addFinger cont st = st {fingerTable = foldl pred (fingerTable st) [1..(fromIntegral $ m st)]}
    where pred a b
            | Just True <- liftM (\x -> cNodeId x < c) $ Map.lookup b a -- Is the new node closer?
            , let fv = fingerVal st b in ((n < fv) && ((fv < c) || (c < n))) || ((fv < n) && (fv < c) && (c < n))
            = Map.insert b cont a
            | Nothing <- liftM (\x -> cNodeId x < c) $ Map.lookup b a -- Is the new node closer?
            , let fv = fingerVal st b in ((n < fv) && ((fv < c) || (c < n))) || ((fv < n) && (fv < c) && (c < n))
            = Map.insert b cont a
            | otherwise = a

          c = cNodeId cont
          n = cNodeId (self st)
fingerVal ::  (Integral a) => NodeState -> a -> Integer
fingerVal st k = mod ((cNodeId . self $ st) + 2^(k-1)) (2^(fromIntegral $ m st))
-- }}}

-- {{{ State stuff
data PassState = GetState ProcessId | PutState NodeState | RetState NodeState deriving (Show, Typeable)

instance Binary PassState where
  put (GetState pid) = do put (0 :: Word8)
                          put pid
  put (PutState i) = do put (1 :: Word8)
                        put i
  put (RetState i) = do put (2 :: Word8)
                        put i
  get = do
        flag <- getWord8
        case flag of
          0 -> do
               pid <- get
               return (GetState pid)
          1 -> do
               i <- get
               return (PutState i)
          2 -> do
               i <- get
               return (RetState i)

getState :: ProcessM NodeState
getState = do nodeId <- getSelfNode
              let process = ProcessId nodeId 7
              pid <- getSelfPid
              send process (GetState pid)
              (RetState a) <- expect
              return a

putState :: NodeState -> ProcessM ()
putState st = do nodeId <- getSelfNode
                 let process = ProcessId nodeId 7
                 send process (PutState st)
-- }}}

-- | someone asks you for a successor, if you know it you reply to the original caller,
-- | else you relay the query forward
relayFndSucc :: (NodeId, ProcessId, Key) -> ProcessM ()
relayFndSucc (nid, caller, key) = do
  st' <- getState
  let st = addFinger (nodeFromPid caller) (addFinger nid st')
  say (show (fingerTable st))
  putState st
  --say (show $ hasSuccessor st key)
  case (hasSuccessor st key) of
      (Just suc) -> send caller suc -- send the ORIGINAL caller the answer.
      _ -> do
          recv <- closestPreceding st key -- | find the next to relay to
          case recv == (nodeFromPid caller) of
            False -> do selfClosure <- makeClosure "Main.relayFndSucc__impl" (self st, caller, key)
                        spawn recv selfClosure
	                return ()
            True -> do self <- getSelfNode
                       send caller self -- We've detected a circle, we cant say NodeA's sucessor is NodeA
                       return ()

$( remotable ['relayFndSucc] )

joinChord :: NodeId -> ProcessM ()
joinChord node = do
    st <- getState
    selfPid <- getSelfPid
    spawn node (relayFndSucc__closure (self st, selfPid, (cNodeId . self $ st)))
    succ <- expect :: ProcessM NodeId -- ^ TODO should time out and retry
    --updSt <- buildFingers succ
    --putState (updSt {fingerTable = (Map.insert 1 succ (fingerTable updSt)) })
    sst <- getState
    return ()

-- | YOU are wordering who's the successor of a certain key, if you don't know yourself
-- | you relay it forward with YOU as the original caller.
findSuccessor :: Key -> ProcessM NodeId
findSuccessor key = do
  st <- getState
  case (hasSuccessor st key) of
      (Just suc) -> return suc -- You self have the successor for the node
      _ -> do
          selfPid <- getSelfPid -- ^ get your pid
          recv <- closestPreceding st key -- ^ find the next to relay to
          spawn recv (relayFndSucc__closure (self st, selfPid, (cNodeId . self $ st)))
          succ <- expect :: ProcessM NodeId -- ^ TODO should time out and retry
          return succ

-- {{{ buildFingers
buildFingers :: NodeId -> ProcessM NodeState
buildFingers c = do
                      st <- getState
                      nodeId <- getSelfNode
                      let f = findSuccessor
                          fsid i = (cNodeId (self st)) + (2 ^ (i - 1))
                          nodids = map fsid r
                          r = [1 .. (fromIntegral . m $ st)]
                      fingers <- sequence $ map f nodids
                      let newSt = st {fingerTable = Map.fromList $ zip r fingers}
                      return newSt
-- }}}

bootStrap st _ = do
  selfN <- getSelfNode
  let st' = st { self = selfN, predecessor = selfN }
  peers <- getPeers
  let peers' = findPeerByRole peers "NODE"
  case length peers' > 1 of
    True -> do
             say $ "Found peers: "  ++ (show peers')
             let nSt = addFinger (head . (drop 1) $ peers') st'
             spawnLocal (joinChord (head . (drop 1) $ peers'))
             handleState nSt
    False -> do
             --spawnLocal (joinChord selfN)
             let newSt = st' -- { fingerTable= Map.insert 160 selfN (fingerTable st') }
             handleState newSt



-- | handlet get and puts for the state
handleState st = do
  pid <- getSelfPid
  updSt <- receiveWait (map match [hsGet])
  handleState updSt
  where hsGet (GetState pid) = send pid (RetState st) >> return st
        hsGet (PutState nSt) = return nSt

main = remoteInit Nothing [Main.__remoteCallMetaData] (bootStrap initState)

initState = NodeState {
          self = undefined
        , fingerTable = Map.empty -- ^ The fingerTable
        , predecessor = undefined
        , timeout = 10 -- ^ The timout latency of ping
        , m = 160 -- ^ The number of bits in a key, ususaly 160
        , alpha = 4 -- ^ The number of parralell queries
        }
