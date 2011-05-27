{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
module Chord where

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
        , bootstrapNode :: NodeId -- ^ A node in the network
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
	     put (bootstrapNode a)
  get = do se <- get
           ft <- get
	   pr <- get
	   ti <- get
	   m <- get
	   a <- get
	   bn <- get
	   return (NodeState { self = se, fingerTable = ft, predecessor = pr, timeout = ti, m=m, alpha=a, bootstrapNode=bn })

successor :: NodeState -> Maybe NodeId
successor st = helper st 1
    where helper st k
            | fromIntegral k > (m st) = Nothing
            | Just c <- Map.lookup k (fingerTable st) = Just c
            | otherwise = helper st (k+1)

type Key = Integer


data FndMsg = FndSucc ProcessId Key | RspFndSucc NodeId deriving (Show, Typeable)
instance Binary FndMsg where
   put (FndSucc p k) = do
                         put (0 :: Word8)
                         put p
                         put k
   put (RspFndSucc c) = do
                         put (1 :: Word8)
                         put c
   get = do
           flag <- getWord8
           case flag of
             0 -> do
                   p <- get
                   k <- get
                   return (FndSucc p k)
             1 -> do
                   c <- get
                   return (RspFndSucc c)

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
  | Map.null conts = (self st)
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

data PassState = GetState ProcessId | PutState NodeState | RetState NodeState deriving (Show, Typeable)

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

-- | someone asks you for a successor, if you know it you reply to the original caller,
-- | else you relay the query forward
relayFndSucc :: (ProcessId, Key) -> ProcessM ()
relayFndSucc (caller, key) = do
  st <- getState
  case (hasSuccessor st key) of
      (Just suc) -> send caller (RspFndSucc suc) -- send the ORIGINAL caller the answer.
      _ -> do
          recv <- closestPreceding st key -- | find the next to relay to
          selfClosure <- makeClosure "Chord.relayFndSucc__impl" (caller, key)
          spawn recv selfClosure
	  return ()

$( remotable ['relayFndSucc] )

handleQueries port = do
   (FndSucc pid key) <- receiveChannel port
   spawnLocal $ relayFndSucc (pid, key)
   handleQueries port

joinChord :: NodeId -> ProcessM ()
joinChord node = do
    st <- getState
    selfPid <- getSelfPid
    --sendChannel (cPort node) (FndSucc selfPid (cNodeId . self $ st))
    (RspFndSucc succ) <- expect -- ^ TODO should time out and retry

    --buildFingers tSt succ
    putState (st {fingerTable = (Map.insert 1 succ (fingerTable st)) })
    return ()


-- | YOU are wordering who's the successor of a certain key, if you don't know yourself
-- | you relay it forward with YOU as the original caller.
findSuccessor :: ProcessId -> Key -> ProcessM NodeId
findSuccessor caller key = do
  st <- getState
  case (hasSuccessor st key) of
      (Just suc) -> return suc -- You self have the successor for the node
      _ -> do
          selfPid <- getSelfPid -- ^ get your pid
          recv <- closestPreceding st key -- | find the next to relay to
          let msg = FndSucc selfPid key -- ^ Construct a message to send
          --sendChannel (cPort recv) msg  -- ^ Send it
          (RspFndSucc succ) <- expect   -- ^ TODO should time out and retry
          return succ



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

-- | handlet get and puts for the state
handleState st = do
  updSt <- receiveWait (map match [hsGet])
  handleState updSt
  where hsGet (GetState pid) = send pid (RetState st) >> return st
        hsGet (PutState nSt) = return nSt
