{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
module DHash where

--TODO the node responsible for a key needs some way of telling other nodes how to replicate it's key.
--the nodes that take the burden for replicating also needs some way of verifing that they have the responsebility for the block

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
getBlock key = do
    succ <- findSuccessor key
    getBlock' key succ

getBlock' :: Integer -> [NodeId] -> ProcessM (Maybe BS.ByteString)
getBlock' _ [] = return Nothing
getBlock' key (s:su) = do
    blockPid <- getBlockPid s
    selfPid <- getSelfPid
    flag <- ptry $ send blockPid (Lookup key selfPid) :: ProcessM (Either TransmitException ())
    block <- receiveTimeout 10000000 [match (\x -> return x)] :: ProcessM (Maybe Block)
    case block of
      Nothing -> say "GetBlock timed out, retrying" >> getBlock' key su
      Just BlockError -> say "Block error" >> getBlock' key su
      Just (BlockFound bs) -> if encBlock bs == key
                                then return (Just bs)
                                else return Nothing
-- }}}

-- {{{ putBlock, puts a block, returns the successor of that block. You will
-- also find the block replicated on the (r st) next nodes
putBlock ::  BS.ByteString -> ProcessM (Integer, NodeId)
putBlock bs = do
    let key = encBlock bs
    succs <- findSuccessor key
    ns <- putBlock' bs (head succs)
    return (key, ns)

-- | putBlock' put a block on a node we know
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

data DHash = Insert BS.ByteString | Lookup Integer ProcessId | Delete Integer | Janitor deriving (Eq, Show, Typeable)
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

type DHashTable = HT.LinearHashTable Integer (Bool,BS.ByteString)

sendBlock :: Maybe (Bool, BS.ByteString) -> ProcessId -> ProcessM ()
sendBlock Nothing pid = do ptry (send pid BlockError) :: ProcessM (Either TransmitException ())
                           return ()
sendBlock (Just (_, bs)) pid = do ptry (send pid (BlockFound bs)) :: ProcessM (Either TransmitException ())
                                  return ()

initBlockStore :: DHashTable -> ProcessM ()
initBlockStore ht' = do
  nameSet "DHASH-BLOCK-STORE"
  spawnLocal sceduler
  loop ht'
  where loop :: DHashTable -> ProcessM ()
        loop ht = do
            newHt <- receiveWait
              [ matchIf (\x -> case x of
                                 (Insert _) -> True
                                 _ -> False)
                        (\(Insert val) -> jok ht val)
              , matchIf (\x -> case x of
                               (Lookup _ _) -> True
                               _ -> False)
                        (\(Lookup key pid) -> lok key pid ht)
              , matchIf (\x -> case x of
                               Janitor -> True
                               _ -> False)
                        (\Janitor -> janitor ht)
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

        jok :: DHashTable -> BS.ByteString -> ProcessM DHashTable
        jok ht val = do let key = encBlock val
                        st <- getState
                        if between key (cNodeId . predecessor $ st) (cNodeId . self $ st)
                          then do liftIO $ HT.insert ht key (True, val)
                                  mapM (putBlock' val) (successors st)
                                  return ht
                          else do liftIO $ HT.insert ht key (False, val)
                                  say "replicating"
                                  return ht

janitor :: DHashTable -> ProcessM DHashTable
janitor ht = do ns <- liftIO $ HT.toList ht
                st <- getState
                ns' <- mapM (fix st) ns
                liftIO $ HT.fromList ns'

sceduler :: ProcessM ()
sceduler = do
         self <- getSelfNode
         pid <- getBlockPid self
         loop pid
  where loop pid = do
             liftIO (threadDelay 5000000)
             send pid Janitor
             loop pid

fix :: NodeState -> (Integer, (Bool,BS.ByteString)) -> ProcessM (Integer, (Bool,BS.ByteString))
fix st entry@(key, (True, bs)) = do
   if between key (cNodeId . predecessor $ st) (cNodeId . self $ st)
     then return entry
     else do 
             say "we are no longer responsible for this block"
             putBlock bs
             return (key,(False,bs))

fix st entry@(key, (False, bs)) = do
   if between key (cNodeId . predecessor $ st) (cNodeId . self $ st)
     then do 
             say "we are the new block owner"
             mapM_  (putBlock' bs) (successors st)
             return (key,(True,bs))
     else return entry
