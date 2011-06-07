{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
module Main where

import Remote
import Remote.Call

import System.Random(randomRIO)
import Control.Monad.Trans(liftIO)

spawner :: ProcessM ()
spawner = do
  thisNode <- getSelfNode -- This could also be a remote node
  flag <- liftIO $ randomRIO (0,100) :: ProcessM Int
  case flag of
    1 -> say "Got one"
    x -> do selfClosure <- makeClosure "Main.spawner__impl" ()
            say ("Get " ++ (show x)) >> spawn thisNode (selfClosure) >> return ()

remotable ['spawner]

initial _ = do spawnLocal spawner
               return ()

main = remoteInit Nothing [Main.__remoteCallMetaData] initial
