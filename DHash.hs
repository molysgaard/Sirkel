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

import qualified Data.HashTable.IO as HT
import Control.Monad.ST

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
getBlock :: Integer -> ProcessM (Maybe BS.ByteString)
getBlock key = getBlock' key 3

getBlock' :: Integer -> Int -> ProcessM (Maybe BS.ByteString)
getBlock' _ 0 = return Nothing
getBlock' key n = do
    succ <- liftM head $ findSuccessor key
    blockPid <- getBlockPid succ
    selfPid <- getSelfPid
    flag <- ptry $ send blockPid (Lookup key selfPid) :: ProcessM (Either TransmitException ())
    block <- receiveTimeout 10000000 [match (\x -> return x)] :: ProcessM (Maybe Block)
    case block of
      Nothing -> say "GetBlock timed out, retrying" >> getBlock' key (n-1)
      Just BlockError -> say "Block error" >> liftIO (threadDelay 5000000) >> getBlock' key (n-1)
      Just (BlockFound bs) -> if encBlock bs == key
                                then return (Just bs)
                                else return Nothing
-- }}}

-- {{{ putBlock
putBlock bs = do
    let key = encBlock bs
    succs <- findSuccessor key
    ns <- mapM (putBlock' bs) succs
    return (key, ns)

putBlock' :: BS.ByteString -> NodeId -> ProcessM NodeId
putBlock' bs succ = do
    pid <- getBlockPid succ
    flag <- ptry $ send pid (Insert bs) :: ProcessM (Either TransmitException ())
    case flag of
      Left _ -> say "put block failed, retrying" >> (liftIO (threadDelay 5000000)) >> putBlock' bs succ
      Right _ -> return succ
-- }}}

getBlockPid :: NodeId -> ProcessM ProcessId
getBlockPid node = do 
                 statePid <- nameQuery node "DHASH-BLOCK-STORE"
                 case statePid of
                   Nothing -> say "Dhash block store not initialized, state-process is not running" >> (liftIO (threadDelay 5000000)) >> getStatePid
                   Just pid -> return pid

data DHash = Insert BS.ByteString | Lookup Integer ProcessId | Delete Integer deriving (Eq, Show, Typeable)
instance Binary DHash where
  put (Insert a) = do put (0 :: Word8)
                      put a
  put (Lookup key pid) = do put (1 :: Word8)
                            put key
                            put pid
  put (Delete key) = do put (2 :: Word8)
                        put key
  get = do flag <- getWord8
           case flag of
             0 -> do val <- get
                     return $ Insert val
             1 -> do key <- get
                     pid <- get
                     return $ Lookup key pid
             2 -> do key <- get
                     return $ Delete key

type DHashTable = HT.LinearHashTable Integer BS.ByteString

sendBlock :: Maybe BS.ByteString -> ProcessId -> ProcessM ()
sendBlock Nothing pid = do ptry (send pid BlockError) :: ProcessM (Either TransmitException ())
                           return ()
sendBlock (Just bs) pid = do ptry (send pid (BlockFound bs)) :: ProcessM (Either TransmitException ())
                             return ()

initBlockStore :: DHashTable -> ProcessM ()
initBlockStore ht' = do
  nameSet "DHASH-BLOCK-STORE"
  loop ht'
  where loop :: DHashTable -> ProcessM ()
        loop ht = do
            newHt <- receiveWait
              [ matchIf (\x -> case x of
                                 (Insert _) -> True
                                 _ -> False)
                        (\(Insert val) -> jok ht (encBlock val) val)
              , matchIf (\x -> case x of
                               (Lookup _ _) -> True
                               _ -> False)
                        (\(Lookup key pid) -> lok key pid ht)
              , matchIf (\x -> case x of
                               (Delete _) -> True
                               _ -> False)
                        (\(Delete key) -> tok ht key) ]
            loop newHt

        lok :: Integer -> ProcessId -> DHashTable -> ProcessM DHashTable
        lok key pid ht = do answ <- liftIO $ HT.lookup ht key
                            spawnLocal (sendBlock answ pid)
                            return ht

        tok :: DHashTable -> Integer -> ProcessM DHashTable
        tok ht key = do liftIO $ HT.delete ht key
                        return ht

        jok :: DHashTable -> Integer -> BS.ByteString -> ProcessM DHashTable
        jok ht key val = do liftIO $ HT.insert ht key val
                            return ht
