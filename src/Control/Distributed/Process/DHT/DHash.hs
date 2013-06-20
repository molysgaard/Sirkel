{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
module Control.Distributed.Process.DHT.DHash (
                        -- * Initialization
                        initBlockStore,
                        -- * Put/Get/Delete
                        putObject,
                        getObject,
                        deleteBlock,
                        -- * Utility
                        encBlock
                        ) where

--TODO A block is put on node A and replicated on node B.
--     Then node B leaves.
--     Then the next node in the ring, node C, does not recieve a replicate command.
--     Only if node A leaves and there exits replicas will the replicas be correctly reinserted.

import Control.Concurrent (threadDelay)
import Control.Monad (liftM,void)
import Data.Digest.Pure.SHA
import Data.Binary
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.HashTable.IO as HT
import Data.Maybe
import Data.Typeable
import GHC.Generics

import Control.Distributed.Process

import Control.Distributed.Process.DHT.Chord hiding (__remoteTable)

-- | 'Block' lets us send blocks back when somone asks for one.
data Block = BlockError | BlockFound BS.ByteString deriving (Show, Typeable,Generic)
instance Binary Block

-- | 'encBlock' takes a 'BS.ByteString' and returns the ID/key
-- of that block. This is for 'BS.ByteString's what 'cNodeId' is for 'NodeId's
encBlock :: BS.ByteString -> Integer
encBlock n = integerDigest . sha1 $ n

-- | 'getBlock' retrieves a block with a given ID/key.
getBlock :: Integer -> Int -> Process (Maybe BS.ByteString)
getBlock key howMany = do
    succN <- findSuccessors key howMany
    getBlock' key howMany succN

-- | internal function for 'getBlock'
--   'getBlock' gets a block from a node we know has it
getBlock' :: Integer -> Int -> [NodeId] -> Process (Maybe BS.ByteString)
getBlock' _ _ [] = return Nothing
getBlock' key howMany (s:su) = do
    ret <- getBlockPid s
    case ret of
      Just blockPid -> do
          selfPid <- getSelfPid
          -- flag <- ptry $ send blockPid (Lookup key selfPid) :: Process (Either TransmitException ())
          send blockPid (Lookup key selfPid) -- :: Process (Either TransmitException ())
          block <- receiveTimeout 10000000 [match return] :: Process (Maybe Block)
          case block of
            Nothing -> say "GetBlock timed out, retrying" >> liftIO (threadDelay 5000000) >> getBlock key howMany
            Just BlockError -> say "Block error" >> getBlock' key howMany su
            Just (BlockFound bs) -> return (if encBlock bs == key then Just bs else Nothing)
      Nothing -> say "GetBlock timed out, retrying" >> liftIO (threadDelay 5000000) >> getBlock key howMany

-- | 'putBlock', puts a block, returns the successor of that block. You will
-- also find the block replicated on the (r st) next nodes, but it is the node
-- responsible for the block that is responsible for delivering the block to the
-- replicators.
putBlock ::  BS.ByteString -> Process (Integer, NodeId)
putBlock bs = do
    let key = encBlock bs
    succs <- findSuccessors key 1
    putBlock' bs key (head succs)

-- | 'putBlock'' put a block on a node we know
putBlock' :: BS.ByteString -> Integer -> NodeId -> Process (Integer, NodeId)
putBlock' bs key succN = do
    ret <- getBlockPid succN
    case ret of
      Just pid -> do
          send pid (Insert bs)
          return (key,succN)
          {-
          flag <- ptry $ send pid (Insert bs) :: Process (Either TransmitException ())
          case flag of
            Left _ -> say "put block failed, retrying" >> (liftIO (threadDelay 5000000)) >> putBlock bs
            Right _ -> return (key, succ)
          -}
      Nothing -> say "put block failed, retrying" >> (liftIO (threadDelay 5000000)) >> putBlock bs

-- | 'deleteBlock' takes the ID/key of the block to delete
-- and sends a message to the node responsible for that block.
-- The message then propagates from the responsible to the
-- replicators.
deleteBlock :: Integer -> Process Bool
deleteBlock key = do
    succs <- findSuccessors key 1
    ret <- getBlockPid (head succs)
    case ret of
      Just blockPid -> do
          send blockPid (Delete key)
          return True
          {-
          flag <- ptry $ send blockPid (Delete key) :: Process (Either TransmitException ())
          case flag of
            Left _ -> say "Delete failed" >> return False
            Right _ -> say "Delete sent" >> return True
          -}
      Nothing -> say "Delete failed" >> return False

-- | 'getBlockPid' gets the 'ProcessId' for the 'initBlockStore' process.
getBlockPid :: NodeId -> Process (Maybe ProcessId)
getBlockPid node = do
                 -- statePid <- ptry $ nameQuery node "DHASH-BLOCK-STORE" :: Process (Either ServiceException (Maybe ProcessId))
                 whereisRemoteAsync node "DHASH-BLOCK-STORE"
                 (WhereIsReply _str statePid) <- expect
                 case statePid of
                   (Just pid) -> return (Just pid)
                   _ -> say "Dhash block store not initialized, state-process is not running" >> return Nothing

-- | 'Dhash' is a datatype encapsulating the things we can do with the HashTable
data DHash = Insert BS.ByteString | Lookup Integer ProcessId | Delete Integer | Janitor deriving (Eq, Show, Typeable,Generic)
instance Binary DHash

-- | 'DHashTable' is the datastructure used to store all blocks.
-- This is designed so that in the future we can extend it to
-- other storage systems, eg. filesystem.
type DHashTable = HT.LinearHashTable Integer (Bool,BS.ByteString)

-- | sendBlock is a function to send a block from a lookup in the HashTable.
-- We do this in a separate thread because we don't want to block lookups etc.
-- while we are sending.
-- TODO there have to be some sort of queue here in the future, to limit the
-- upload
sendBlock :: Maybe (Bool, BS.ByteString) -> ProcessId -> Process ()
sendBlock Nothing pid = do
    (send pid BlockError) -- :: Process (Either TransmitException ())
    return ()
sendBlock (Just (_, bs)) pid = do
    (send pid (BlockFound bs)) -- :: Process (Either TransmitException ())
    return ()

-- | initBlockStore starts the BlockStore and handles requests to
-- insert, lookup and delete blocks as well as the janitor process
-- to check if ownership of any block has changed
initBlockStore :: DHashTable -> Process ()
initBlockStore ht' = do
  myPid <- getSelfPid
  register "DHASH-BLOCK-STORE" myPid
  void $ spawnLocal janitorSceduler
  loop ht'
  where loop :: DHashTable -> Process ()
        loop ht = do
            newHt <- receiveWait
              [ matchIf (\x -> case x of
                                 (Insert _) -> True
                                 _ -> False)
                        (\(Insert val) -> insertBlock ht val)
              , matchIf (\x -> case x of
                               (Lookup _ _) -> True
                               _ -> False)
                        (\(Lookup key pid) -> lookupBlock key pid ht)
              , matchIf (\x -> case x of
                               Janitor -> True
                               _ -> False)
                        (\Janitor -> janitor ht)
              , matchIf (\x -> case x of
                               (Delete _) -> True
                               _ -> False)
                        (\(Delete key) -> removeBlock ht key) ]
            loop newHt

-- | looks in the hashtable for the block and returns it if it finds it.
lookupBlock :: Integer -> ProcessId -> DHashTable -> Process DHashTable
lookupBlock key pid ht = do answ <- liftIO $ HT.lookup ht key
                            void $ spawnLocal (sendBlock answ pid)
                            return ht

-- | removes a block from the hash table if it exists there.
removeBlock :: DHashTable -> Integer -> Process DHashTable
removeBlock ht key = do
    st <- getState
    -- if we are the owner of the block, also send delete
    -- to all the replicas
    -- else just delete our copy
    if between key (cNodeId . predecessor $ st) (cNodeId . self $ st)
      then do liftIO $ HT.delete ht key
              bs <- liftM catMaybes $ mapM getBlockPid (successors st)
              say "deleting replicas"
              mapM_ ((flip send) (Delete key)) bs
              return ht
      else do liftIO $ HT.delete ht key
              return ht

-- | Inserts a block to the 'DHashTable'. It also checks if we
-- are the node responsible for the block or just a replicator.
insertBlock :: DHashTable -> BS.ByteString -> Process DHashTable
insertBlock ht val = do
  st <- getState
  -- if the block is to big, we won't store it because somethings wrong
  if BS.null (BS.drop (blockSize st) val)
    then do
      let key = encBlock val
      -- if we are the right owner of this block
      -- or if we are just replicating
      -- TODO would be smart to check if we should be
      -- replicating but it is not trivial without a predecessor list
      -- wich is not implemented at this time
      if between key (cNodeId . predecessor $ st) (cNodeId . self $ st)
        then do liftIO $ HT.insert ht key (True, val)
                mapM_ (putBlock' val key) ((take (b st)) . successors $ st)
                return ht
        else do liftIO $ HT.insert ht key (False, val)
                say "replicating"
                return ht
    else return ht

-- | janitor takes the DHashTable and checks if the ownership of blocks
-- has changed sice last time. If so it updates replication etc.
janitor :: DHashTable -> Process DHashTable
janitor ht = do ns <- liftIO $ HT.toList ht
                st <- getState
                ns' <- mapM (fix st) ns
                liftIO $ HT.fromList ns'

-- | janitorSceduler is a process that periodically sends a "janitor"
-- message to the block manager, this because we don't have MVars in
-- CloudHaskell
janitorSceduler :: Process ()
janitorSceduler = do
         myNode <- getSelfNode
         ret <- getBlockPid myNode
         case ret of
           Just pid -> loop pid
           Nothing -> say "janitoring cant start before block store, retrying" >> liftIO (threadDelay 50000000) >> janitorSceduler
  where loop pid = do
             liftIO (threadDelay 5000000)
             send pid Janitor
             loop pid

-- | fix function that looks on one block in the HashTable
-- and checks if ownership hash changed.
fix :: NodeState -> (Integer, (Bool,BS.ByteString)) -> Process (Integer, (Bool,BS.ByteString))
fix st entry@(key, (True, bs))
  | between key (cNodeId . predecessor $ st) (cNodeId . self $ st)
  = return entry
  | otherwise = do
             say "we are no longer responsible for this block"
             void $ putBlock bs
             return (key,(False,bs))

fix st entry@(key, (False, bs))
  | between key (cNodeId . predecessor $ st) (cNodeId . self $ st)
  = do
      say "we are the new block owner"
      mapM_  (putBlock' bs key) (successors st)
      return (key,(True,bs))
  | otherwise = return entry

-- | 'chunkBs' splits a 'BS.ByteString' into parts that
-- each has the size of 'blockSize' bytes or less.
chunkBs ::  NodeState -> BS.ByteString -> [BS.ByteString]
chunkBs st bs
  | BS.null bs = []
  | otherwise  = let (pre, post) = BS.splitAt (blockSize st) bs
                 in pre : chunkBs st post

-- | 'putObject' is the main function of the DHash module.
-- It lets you put an arbitrary object that an instance of
-- Binary into the DHT. To retrieve it again, you'll have to call
-- 'getObject' with the list of IDs/keys that this function returns.
-- NB: The order of the IDs/keys matters. This is because an object is
-- chunked. Then each chunk is stored seperatly. When one calls 'getObject'
-- the blocks retrieved is concated in the order of the IDs/keys.
-- That means you'll get garbage if you mess up the order.
putObject ::  (Binary a) => a -> Process [(Integer, NodeId)]
putObject a = do st <- getState
                 let bs = (chunkBs st) . encode $ a
                 mapM putBlock bs

-- | 'getObject' takes a list of IDs/keys that represent an object that's
-- already been put with 'putObject'.
-- NB: The order of the IDs/keys matters. This is because an object is
-- chunked. Then each chunk is stored seperately. When one calls 'getObject'
-- the blocks retrieved is concated in the order of the IDs/keys.
-- That means you'll get garbage if you mess up the order.
getObject ::  (Binary a) => [Integer] -> Int -> Process (Maybe a)
getObject keys howMany = liftM (liftM decode . maybeConcatBS) (mapM (`getBlock` howMany) keys)

-- | 'maybeConcatBS' takes '[Maybe BS.ByteString]'s and concats
-- all the bytestrings into one if none of them are Nothing.
-- Else it returns Nothing
maybeConcatBS ::  [Maybe BS.ByteString] -> Maybe BS.ByteString
maybeConcatBS blocks
  | Nothing `elem` blocks = Nothing
  | otherwise = Just . BS.concat . catMaybes $ blocks
