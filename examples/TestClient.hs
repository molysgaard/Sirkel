{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
module Main where

import Control.Distributed.Process
import Control.Distributed.Process.Platform.Call
import Control.Distributed.Process.Platform.Async
import Control.Distributed.Process.Closure
import Control.Distributed.Process.Node -- (initRemoteTable)
import Network.Transport.TCP

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
import qualified Data.ByteString.Lazy.Char8 as BS
import System.IO (hGetLine, stdin)
-- for helper/debug
import qualified Data.List as List
import System.Random (randomRIO)
import Data.Ratio
import Data.Maybe (fromJust)

import qualified Data.HashTable.IO as HT

import qualified Control.Distributed.Process.DHT.Chord as Chord
import qualified Control.Distributed.Process.DHT.DHash as DHash

import Control.Distributed.Process.DHT.Chord
import Control.Distributed.Process.DHT.DHash

main = do
    Right transport <- createTransport "127.0.0.1" "8080" defaultTCPParameters
    let rtable = Chord.__remoteTable . Chord.__remoteTableDecl $ initRemoteTable
    node <- newLocalNode transport rtable
    runProcess node $ do
      bootstrap initState node -- ^ Start the chord ring
      spawnLocal randomFinds -- ^ do some random lookups in the chord ring at intervals, just for debug
      ht <- liftIO $ HT.new -- ^ make a new empty hashtable, if we want we can use a non empty table, eg the one from last time the client run.
      spawnLocal $ initBlockStore ht -- ^ spawn the block store. this one handles puts, gets and deletes
      userInput -- ^ this is for debug, it's our window into whats happening ;)

-- {{{ userInput
-- | debug function, reads a 0.[0-9] number from command line and runs findSuccessors on it in the DHT
userInput :: Process ()
userInput = do line <- liftIO $ hGetLine stdin
               st <- getState
               let x = 2^160 :: Integer
                   fm :: Integer -> Double
                   fm = fromRational . (% x)
                   sh = (take 5) . show
               case (take 3 line) of
                  "put" -> do holder <- putObject (drop 4 line)
                              say . show . (map fst) $ holder
                  "get" -> do resp <- getObject ((read (drop 4 line)) :: [Integer]) (r st) :: Process (Maybe String)
                              say $ show resp
                  "fnd" -> do let num = truncate ((read (drop 4 line)) * (fromInteger x)) :: Integer
                              tmp_howMany <- liftIO $ hGetLine stdin
                              let howMany = read tmp_howMany :: Int
                              succ <- Chord.findSuccessors num howMany
                              say $ show . (map (fm . cNodeId)) $ succ
                  "del" -> do let num = ((read (drop 4 line)) :: Integer)
                              succ <- deleteBlock num
                              say $ "Trying to delete: " ++ (show num)
                  "sta" -> do st <- getState
                              say (show st)
                  "id" -> do st <- getState
                             say $ sh . fm . cNodeId . self $ st
                  _ -> return ()
               userInput
-- }}}

initState = Chord.NodeState {
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

-- {{{ randomFinds
-- | This is a debug function, it periodically requests to know the sucessor of a random key in the ring
randomFinds = do
  liftIO $ threadDelay 8000000 -- 8 sec
  st <- getState
  key <- liftIO $ randomRIO (1, 2^(m st)) :: Process Integer
  succ <- findSuccessors key (r st)
  let x = 2^(m $ st) :: Integer
      fm :: Integer -> Double
      fm = fromRational . (% x)
      --sh = (take 5) . show
  --say $ (sh . fm . cNodeId . self $ st) ++ " says succ " ++ (sh . fm $ key) ++ " is " ++ (sh . fm . cNodeId $ succ)
  randomFinds
-- }}}
