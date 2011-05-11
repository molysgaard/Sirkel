{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards #-}
module Main where

import Remote.Call
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
import Control.Monad.State

import Control.Concurrent
import Control.Concurrent.STM
import qualified Data.Map as Map

import Data.Digest.Pure.SHA
import Data.Binary

import DataTypes
--import Logic

data RspFndSucc = RspFndSucc NodeId
data FndSucc = FndSucc ProcessId

cNodeId node = integerDigest . sha1 $ encode node

-- | Shuld return the successor of US if the key asked for is BETWEEN us an the successor
hasSuccessor :: TVar NodeState -> Key -> STM (Maybe NodeId)
hasSuccessor tVarSt key = do
   st <- readTVar tVarSt
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

-- | someone asks you for a successor, if you know it you reply to the original caller,
-- | else you relay the query forward
relayFndSucc :: TVar NodeState -> ProcessId -> Key -> ProcessM ()
relayFndSucc st caller key = do
  successor <- liftIO $ atomically (hasSuccessor st key)
  case successor of
      (Just suc) -> send caller (RspFndSucc suc) -- send the ORIGINAL caller the answer.
      _ -> do
          recv <- liftIO . atomically $ closestPreceding st key -- | find the next to relay to
          let remFndSucc = do ($(mkClosure 'relayFndSucc) caller (FndSucc key)) -- | make the remote call
          spawn recv remFndSucc
remotable ['relayFndSucc ]


{--
-- | YOU are wordering who's the successor of a certain key, if you don't know yourself
-- | you relay it forward with YOU as the original caller.
findSuccessor :: Integer -> ProcessM (Maybe RspFndSucc successor)
findSuccessor st key
  | False = return successor
  | otherwise = do
      self <- getSelfPid
      let recv = closestPreceding st key -- ^ the first one to recieve our query
          remFndSucc = do (relayFndSucc__closure self (FndSucc key)) -- ^ the function he runs
      spawn recv remFndSucc
      return receiveTimeout 10000 [return]

findSuccessor ::  NodeState -> NodeId -> IO (Either String Contact)
findSuccessor st id 
  | (Just suc) <- successor st = do
                         let n = cNodeId (self st)
                         if ((n < id) && (id <= (cNodeId suc)))
                             then return (Right suc)
                             else do
                                    let reciever = closestPrecdingNode st id
                                    case reciever == suc of
                                        True -> return (Right reciever)
                                        False -> remoteFindSuccessor st reciever id
  | otherwise = return $ Left "No fingers"
--}

