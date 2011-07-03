{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
module DHash where

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

import Chord

-- {{{ Block
data Block = BlockError | BlockFound BS.ByteString deriving (Show, Typeable)
instance Binary Block where
  put BlockError = put (0 :: Word8)
  put (BlockFound bs) = do put (1 :: Word8)
                           put bs
  get = do flag <- getWord8
           case flag of
             0 -> return BlockError
             1 -> do bs <- get
                     return $ BlockFound bs
-- }}}

-- {{{ remoteGetBlock
remoteGetBlock :: Integer -> ProcessId -> ProcessM ()
remoteGetBlock key caller = do
    st <- getState
    block <- liftIO $ catch (BS.readFile ((blockDir st) ++ (show key)) >>= (\x -> return $ BlockFound x)) (\e -> return BlockError)
    send caller block
-- }}}

-- {{{ remotePutBlock
remotePutBlock block = do
    st <- getState
    let key = encBlock block
    liftIO $ BS.writeFile ((blockDir st) ++ (show key)) block

encBlock :: BS.ByteString -> Integer 
encBlock n = integerDigest . sha1 $ encode n
-- }}}

$( remotable ['remoteGetBlock, 'remotePutBlock] )

-- {{{ getBlock
getBlock :: Integer -> ProcessM BS.ByteString
getBlock key = do
    succ <- liftM head $ findSuccessor key
    pid <- getSelfPid
    flag <- ptry $ spawn succ (remoteGetBlock__closure key pid)  :: ProcessM (Either TransmitException ProcessId)
    block <- receiveTimeout 10000000 [match (\x -> return x)] :: ProcessM (Maybe Block)
    case block of
      Nothing -> say "GetBlock timed out, retrying" >> getBlock key
      Just (BlockFound bs) -> return bs
      Just BlockError -> say "Block error" >> liftIO (threadDelay 5000000) >> getBlock key
-- }}}

-- {{{ putBlock
putBlock :: BS.ByteString -> ProcessM (NodeId, Integer)
putBlock bs = do
    let key = encBlock bs
    succ <- liftM head $ findSuccessor key
    flag <- ptry $ spawn succ (remotePutBlock__closure bs) :: ProcessM (Either TransmitException ProcessId)
    case flag of
      Left _ -> say "put block failed, retrying" >> (liftIO (threadDelay 5000000)) >> putBlock bs
      Right _ -> return (succ, key)
-- }}}


