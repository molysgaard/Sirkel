{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
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

data PassState = GetState ProcessId | PutState Int | RetState Int deriving (Show, Typeable)

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

bootstrap st _ = do
  spawnLocal asker
  handleState st

-- | handlet get and puts for the state
handleState st = do
  updSt <- receiveWait (map match [hsGet])
  handleState updSt
  where hsGet (GetState pid) = send pid (RetState st) >> return st
        hsGet (PutState nSt) = return nSt

getState :: ProcessM Int
getState = do nodeId <- getSelfNode
              let process = ProcessId nodeId 7
              pid <- getSelfPid
              send process (GetState pid)
              (RetState a) <- expect
              return a

putState :: Int -> ProcessM ()
putState st = do nodeId <- getSelfNode
                 let process = ProcessId nodeId 7
                 send process (PutState st)




main = remoteInit Nothing [] (bootstrap 13)

asker = do
          st <- getState
          say $ "Got state: " ++ (show st)
          putState 7
          st <- getState
          say $ "Got new updated state: " ++ (show st)


