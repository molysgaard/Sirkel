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
          self :: Contact
        , fingerTable :: Map.Map Integer Contact -- ^ The fingerTable
        , predecessor :: Contact
        , timeout :: Int -- ^ The timout latency of ping
        , m :: Int -- ^ The number of bits in a key, ususaly 160
        , alpha :: Int -- ^ The number of parralell queries
        , bootstrapNode :: Contact -- ^ A node in the network
        } deriving (Show)
instance Eq NodeState where
    (==) st1 st2 = ((self st1) == (self st2)) && 
                   ((fingerTable st1) == (fingerTable st2)) &&
                   ((predecessor st1) == (predecessor st2))
    (/=) st1 st2 = not $ (==) st1 st2

successor :: NodeState -> Maybe Contact
successor st = helper st 1
    where helper st k
            | fromIntegral k > (m st) = Nothing
            | Just c <- Map.lookup k (fingerTable st) = Just c
            | otherwise = helper st (k+1)

type Key = Integer

data Contact = Contact NodeId (SendPort FndMsg) deriving (Typeable)
instance Show Contact where
    show (Contact n p) = show n
instance Eq Contact where
   (==) (Contact a _) (Contact b _) = a == b

instance Binary Contact where
  put (Contact id p) = put id >> put p
  get = do
          id <- get
          p  <- get
          return (Contact id p)

data FndMsg = FndSucc ProcessId Key | RspFndSucc Contact deriving (Show, Typeable)
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

cNodeId (Contact n _) = integerDigest . sha1 $ encode n
nodeId (Contact nid _) = nid
cPort (Contact _ p) = p
--}}}

-- | Shuld return the successor of US if the key asked for is BETWEEN us and the successor
hasSuccessor :: TVar NodeState -> Key -> STM (Maybe Contact)
hasSuccessor tVarSt key = do
   st <- readTVar tVarSt
   let n = cNodeId (self st)
       suc = successor st
   case suc of
     Nothing -> return Nothing
     (Just succ) -> if ((n < key) && (key <= (cNodeId succ)))
                    then return (Just succ)
                    else return Nothing

-- | Shuld return the successor of US if the key asked for is BETWEEN us and the successor
hasSuccessorT :: Key -> St.StateT NodeState ProcessM (Maybe Contact)
hasSuccessorT key = do
   st <- St.get
   let n = cNodeId (self st)
       suc = successor st
   case suc of
     Nothing -> return Nothing
     (Just succ) -> if ((n < key) && (key <= (cNodeId succ)))
                    then return (Just succ)
                    else return Nothing

-- {{{ closestPrecedingNode
closestPreceding tvarSt key = do
  st <- readTVar tvarSt
  return $ helper st (fingerTable st) key (fromIntegral . m $ st)

closestPrecedingT key = do
  st <- St.get
  return $ helper st (fingerTable st) key (fromIntegral . m $ st)

helper :: (Ord k, Num k) => NodeState -> Map.Map k Contact -> Key -> k -> Contact
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

-- | someone asks you for a successor, if you know it you reply to the original caller,
-- | else you relay the query forward
relayFndSucc :: TVar NodeState -> ProcessId -> Key -> ProcessM ()
relayFndSucc tSt caller key = do
  successor <- St.liftIO . atomically $ hasSuccessor tSt key
  case successor of
      (Just suc) -> send caller (RspFndSucc suc) -- send the ORIGINAL caller the answer.
      _ -> do
          recv <- St.liftIO . atomically $ closestPreceding tSt key -- | find the next to relay to
          let msg = FndSucc caller key 
          sendChannel (cPort recv) msg

relayFndSuccT :: ProcessId -> Key -> St.StateT NodeState ProcessM ()
relayFndSuccT caller key = do
  successor <- hasSuccessorT key
  case successor of
      (Just suc) -> St.lift $ send caller (RspFndSucc suc) -- send the ORIGINAL caller the answer.
      _ -> do
          recv <- closestPrecedingT key -- | find the next to relay to
          let msg = FndSucc caller key 
          St.lift $ sendChannel (cPort recv) msg

bootStrapChord st bootNode = do
    selfNodeId <- getSelfNode
    (sendPort, receivePort) <- newChannel
    let st = st {self = (Contact selfNodeId sendPort) }
    tSt <- St.liftIO . atomically $ newTVar st
    spawnLocal $ handleQueries tSt receivePort
    --pi <- getPeers
    --let testBoot = head $ findPeerByRole pi "CHORDNODE"
    joinChord tSt bootNode -- testBoot

handleQueries tSt port = do
   (FndSucc pid key) <- receiveChannel port
   spawnLocal $ relayFndSucc tSt pid key
   handleQueries tSt port


--joinChord :: TVar NodeState -> Contact -> STM (ProcessM ())
joinChord tSt node = do
    st <- St.liftIO . atomically $ readTVar tSt

    selfPid <- getSelfPid
    sendChannel (cPort node) (FndSucc selfPid (cNodeId . self $ st))
    (RspFndSucc succ) <- expect -- ^ TODO should time out and retry

    --buildFingers tSt succ
    St.liftIO . atomically $ writeTVar tSt (st {fingerTable = (Map.insert 1 succ (fingerTable st)) })
    return ()

-- | YOU are wordering who's the successor of a certain key, if you don't know yourself
-- | you relay it forward with YOU as the original caller.
findSuccessor :: TVar NodeState -> ProcessId -> Key -> ProcessM Contact
findSuccessor tSt caller key = do
  successor <- St.liftIO . atomically $ hasSuccessor tSt key
  case successor of
      (Just suc) -> return suc -- You self have the successor for the node
      _ -> do
          selfPid <- getSelfPid -- ^ get your pid
          recv <- St.liftIO . atomically $ closestPreceding tSt key -- | find the next to relay to
          let msg = FndSucc selfPid key -- ^ Construct a message to send
          sendChannel (cPort recv) msg  -- ^ Send it
          (RspFndSucc succ) <- expect   -- ^ TODO should time out and retry
          return succ

-- | YOU are wordering who's the successor of a certain key, if you don't know yourself
-- | you relay it forward with YOU as the original caller.
findSuccessorT :: ProcessId -> Key -> St.StateT NodeState ProcessM Contact
findSuccessorT caller key = do
  successor <- hasSuccessorT key
  case successor of
      (Just suc) -> return suc -- You self have the successor for the node
      _ -> do
          selfPid <- St.lift getSelfPid -- ^ get your pid
          recv <- closestPrecedingT key -- | find the next to relay to
          let msg = FndSucc selfPid key -- ^ Construct a message to send
          St.lift $ sendChannel (cPort recv) msg  -- ^ Send it
          (RspFndSucc succ) <- St.lift expect   -- ^ TODO should time out and retry
          return succ
