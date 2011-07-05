{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
module Main where

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
-- for helper debug
import qualified Data.List as List
import System.Random (randomRIO)
import Data.Ratio
import Maybe (fromJust)

import qualified Data.HashTable.IO as HT

import Chord
import DHash
main = remoteInit Nothing [Chord.__remoteCallMetaData, DHash.__remoteCallMetaData] run

run str = do bootStrap initState str
             spawnLocal randomFinds
             ht <- liftIO $ HT.new
             spawnLocal $ initBlockStore ht
             userInput

-- {{{ userInput
-- | debug function, reads a 0.[0-9] number from command line and runs findSuccessor on it in the DHT
userInput :: ProcessM ()
userInput = do line <- liftIO $ hGetLine stdin
               let x = 2^160 :: Integer
                   fm :: Integer -> Double
                   fm = fromRational . (% x)
                   sh = (take 5) . show
               case (take 3 line) of
                  "put" -> do holder <- putBlock (BS.pack (drop 4 line))
                              say $ show holder
                  "get" -> do resp <- getBlock ((read (drop 4 line)) :: Integer)
                              say $ show resp
                  "fnd" -> do let num  = truncate ((read (drop 4 line)) * (fromInteger x)) :: Integer
                              succ <- findSuccessor num
                              say $ sh . fm . cNodeId . head $ succ
                  "del" -> do let num  = ((read (drop 4 line)) :: Integer)
                              succ <- deleteBlock num
                              say $ "Trying to delete: " ++ (show num)
                  "sta" -> do st <- getState
                              say (show st)
                  "id" -> do st <- getState
                             say $ sh . fm . cNodeId . self $ st
                  _ -> return ()
               userInput
-- }}}

initState = NodeState {
          self = undefined
        , fingerTable = Map.empty -- ^ The fingerTable
        , blockDir = "/tmp/"
        , predecessor = undefined
        , timeout = 10 -- ^ The timout latency of ping
        , m = 160 -- ^ The number of bits in a key, ususaly 160
        , r = 2 -- ^ the number of successors and replicas
        }

-- {{{ randomFinds
-- | This is a debug function, it periodically requests to know the sucessor of a random key in the ring
randomFinds = do
  liftIO $ threadDelay 8000000 -- 8 sec
  st <- getState
  key <- liftIO $ randomRIO (1, 2^(m st)) :: ProcessM Integer
  succ <- findSuccessor key
  let x = 2^(m $ st) :: Integer
      fm :: Integer -> Double
      fm = fromRational . (% x)
      --sh = (take 5) . show
  --say $ (sh . fm . cNodeId . self $ st) ++ " says succ " ++ (sh . fm $ key) ++ " is " ++ (sh . fm . cNodeId $ succ)
  randomFinds
-- }}}

