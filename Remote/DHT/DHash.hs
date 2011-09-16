{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
module Remote.DHT.DHash (
                        -- * Initialization
                        initBlockStore,
                        -- * Put/Get/Delete
                        putObject,
                        getObject,
                        deleteBlock,
                        -- * Utility
                        encBlock,
                        -- * Cloud haskell specific
                        Remote.DHT.DHash.__remoteCallMetaData
                        ) where

--TODO A block is put on node A and replicated on node B.
--     Then node B leaves.
--     Then the next node in the ring, node C, does not recieve a replicate command.
--     Only if node A leaves and there exits replicas will the replicas be correctly reinserted

import Remote
import Remote.Process
{--
import Remote.Call
import Remote.Channel
import Remote.Peer
import Remote.Init
import Remote.Encoding
import Remote.Reg
--}

import Control.Monad (liftM)
import Data.Typeable
import Control.Monad.IO.Class (liftIO)

import Control.Concurrent (threadDelay)
import Control.Concurrent.MVar
import qualified Control.Exception as Ex

import qualified Data.Map as Map
import Data.List (foldl')
import Data.Maybe

import Data.Digest.Pure.SHA
import Data.Binary
import qualified Data.ByteString.Lazy.Char8 as BS

import qualified Data.HashTable.IO as HT
import Control.Monad.ST

import Remote.DHT.Chord

-- {{{ Block
-- | 'Block' lets us send blocks back when somone asks for one.
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

-- {{{ encBlock
-- | 'encBlock' takes a 'BS.ByteString' and returns the ID/key
-- of that block. This is for 'BS.ByteString's what 'cNodeId' is for 'NodeId's
encBlock :: BS.ByteString -> Integer 
encBlock n = integerDigest . sha1 $ n
-- }}}

$( remotable [] )

-- {{{ getBlock
-- | 'getBlock' retrieves a block with a given ID/key.
getBlock :: Integer -> Int -> ProcessM (Maybe BS.ByteString)
getBlock key howMany = do
    succ <- findSuccessors key howMany
    getBlock' key howMany succ

-- getBlock' gets a block from a node we know has it
-- | internal function for 'getBlock'
getBlock' :: Integer -> Int -> [NodeId] -> ProcessM (Maybe BS.ByteString)
getBlock' _ _ [] = return Nothing
getBlock' key howMany (s:su) = do
    ret <- getBlockPid s
    case ret of
      Just blockPid -> do
          selfPid <- getSelfPid
          flag <- ptry $ send blockPid (Lookup key selfPid) :: ProcessM (Either TransmitException ())
          block <- receiveTimeout 10000000 [match (\x -> return x)] :: ProcessM (Maybe Block)
          case block of
            Nothing -> say "GetBlock timed out, retrying" >> liftIO (threadDelay 5000000) >> getBlock key howMany
            Just BlockError -> say "Block error" >> getBlock' key howMany su
            Just (BlockFound bs) -> if encBlock bs == key
                                      then return (Just bs)
                                      else return Nothing
      Nothing -> say "GetBlock timed out, retrying" >> liftIO (threadDelay 5000000) >> getBlock key howMany
-- }}}

-- {{{ putBlock
-- | 'putBlock', puts a block, returns the successor of that block. You will
-- also find the block replicated on the (r st) next nodes, but it is the node
-- responsible for the block that is responsible for delivering the block to the
-- replicators.
putBlock ::  BS.ByteString -> ProcessM (Integer, NodeId)
putBlock bs = do
    let key = encBlock bs
    succs <- findSuccessors key 1
    putBlock' bs key (head succs)

-- | 'putBlock'' put a block on a node we know
putBlock' :: BS.ByteString -> Integer -> NodeId -> ProcessM (Integer, NodeId)
putBlock' bs key succ = do
    ret <- getBlockPid succ
    case ret of
      Just pid -> do
          flag <- ptry $ send pid (Insert bs) :: ProcessM (Either TransmitException ())
          case flag of
            Left _ -> say "put block failed, retrying" >> (liftIO (threadDelay 5000000)) >> putBlock bs
            Right _ -> return (key, succ)
      Nothing -> say "put block failed, retrying" >> (liftIO (threadDelay 5000000)) >> putBlock bs
-- }}}

-- {{{ deleteBlock
-- | 'deleteBlock' takes the ID/key of the block to delete
-- and sends a message to the node responsible for that block.
-- The message then propagates from the responsible to the
-- replicators.
deleteBlock :: Integer -> ProcessM Bool
deleteBlock key = do
    succs <- findSuccessors key 1
    ret <- getBlockPid (head succs)
    case ret of
      Just blockPid -> do
          flag <- ptry $ send blockPid (Delete key) :: ProcessM (Either TransmitException ())
          case flag of
            Left _ -> say "Delete failed" >> return False
            Right _ -> say "Delete sent" >> return True
      Nothing -> say "Delete failed" >> return False
-- }}}

-- {{{ getBlockPid
-- | 'getBlockPid' gets the 'ProcessId' for the 'initBlockStore' process.
getBlockPid :: NodeId -> ProcessM (Maybe ProcessId)
getBlockPid node = do 
                 statePid <- ptry $ nameQuery node "DHASH-BLOCK-STORE" :: ProcessM (Either ServiceException (Maybe ProcessId))
                 case statePid of
                   Right (Just pid) -> return (Just pid)
                   _ -> say "Dhash block store not initialized, state-process is not running" >> return Nothing
-- }}}

-- {{{ Datatypes
-- | 'Dhash' is a datatype encapsulating the things we can do with the HashTable
data DHash = Insert BS.ByteString | Lookup Integer ProcessId | Delete Integer | Janitor deriving (Eq, Show, Typeable)
instance Binary DHash where
  put (Insert a) = do put (0 :: Word8)
                      put a
  put (Lookup key pid) = do put (1 :: Word8)
                            put key
                            put pid
  put (Delete key) = do put (2 :: Word8)
                        put key
  put Janitor = do put (3 :: Word8)
  get = do flag <- getWord8
           case flag of
             0 -> do val <- get
                     return $ Insert val
             1 -> do key <- get
                     pid <- get
                     return $ Lookup key pid
             2 -> do key <- get
                     return $ Delete key
             3 -> return Janitor

-- | 'DHashTable' is the datastructure used to store all blocks.
-- This is designed so that in the future we can extend it to 
-- other storage systems, eg. filesystem.
type DHashTable = HT.LinearHashTable Integer (Bool,BS.ByteString)
-- }}}

-- {{{ sendBlock
-- | sendBlock is a function to send a block from a lookup in the HashTable.
-- We do this in a separate thread because we don't want to block lookups etc.
-- while we are sending.
-- TODO there have to be some sort of queue here in the future, to limit the
-- upload
sendBlock :: Maybe (Bool, BS.ByteString) -> ProcessId -> ProcessM ()
sendBlock Nothing pid = do
    ptry (send pid BlockError) :: ProcessM (Either TransmitException ())
    return ()
sendBlock (Just (_, bs)) pid = do
    ptry (send pid (BlockFound bs)) :: ProcessM (Either TransmitException ())
    return ()
-- }}}

-- {{{ initBlockStore
-- | initBlockStore starts the BlockStore and handles requests to
-- insert, lookup and delete blocks as well as the janitor process
-- to check if ownership of any block has changed
initBlockStore :: DHashTable -> ProcessM ()
initBlockStore ht' = do
  nameSet "DHASH-BLOCK-STORE"
  spawnLocal janitorSceduler
  loop ht'
  where loop :: DHashTable -> ProcessM ()
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
-- }}}

-- {{{ lookupBlock
-- | looks in the hashtable for the block and returns it if it finds it.
lookupBlock :: Integer -> ProcessId -> DHashTable -> ProcessM DHashTable
lookupBlock key pid ht = do answ <- liftIO $ HT.lookup ht key
                            spawnLocal (sendBlock answ pid)
                            return ht
-- }}}

-- {{{ removeBlock
-- | removes a block from the hash table if it exists there.
removeBlock :: DHashTable -> Integer -> ProcessM DHashTable
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
-- }}}

-- {{{ insertBlock
-- | Inserts a block to the 'DHashTable'. It also checks if we
-- are the node responsible for the block or just a replicator.
insertBlock :: DHashTable -> BS.ByteString -> ProcessM DHashTable
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
-- }}}

-- {{{ janitor
-- | janitor takes the DHashTable and checks if the ownership of blocks
-- has changed sice last time. If so it updates replication etc.
janitor :: DHashTable -> ProcessM DHashTable
janitor ht = do ns <- liftIO $ HT.toList ht
                st <- getState
                ns' <- mapM (fix st) ns
                liftIO $ HT.fromList ns'
-- }}}

-- {{{ janitorSceduler
-- | janitorSceduler is a process that periodically sends a "janitor"
-- message to the block manager, this because we don't have MVars in
-- CloudHaskell
janitorSceduler :: ProcessM ()
janitorSceduler = do
         self <- getSelfNode
         ret <- getBlockPid self
         case ret of
           Just pid -> loop pid
           Nothing -> say "janitoring cant start before block store, retrying" >> liftIO (threadDelay 50000000) >> janitorSceduler
  where loop pid = do
             liftIO (threadDelay 5000000)
             send pid Janitor
             loop pid
-- }}}

-- {{{ fix
-- | fix function that looks on one block in the HashTable
-- and checks if ownership hash changed.
fix :: NodeState -> (Integer, (Bool,BS.ByteString)) -> ProcessM (Integer, (Bool,BS.ByteString))
fix st entry@(key, (True, bs))
  | between key (cNodeId . predecessor $ st) (cNodeId . self $ st)
  = return entry
  | otherwise = do 
             say "we are no longer responsible for this block"
             putBlock bs
             return (key,(False,bs))

fix st entry@(key, (False, bs))
  | between key (cNodeId . predecessor $ st) (cNodeId . self $ st)
  = do 
      say "we are the new block owner"
      mapM_  (putBlock' bs key) (successors st)
      return (key,(True,bs))
  | otherwise = return entry
-- }}}

-- {{{ chunkBs
-- | 'chunkBs' splits a 'BS.ByteString' into parts that
-- each has the size of 'blockSize' bytes or less.
chunkBs ::  NodeState -> BS.ByteString -> [BS.ByteString]
chunkBs st bs
  | BS.null bs = []
  | otherwise  = let (pre, post) = BS.splitAt (blockSize st) bs
                 in pre : chunkBs st post
-- }}}

-- {{{ putObject
-- | 'putObject' is the main function of the DHash module.
-- It lets you put an arbitrary object that an instance of
-- Binary into the DHT. To retrieve it again, you'll have to call
-- 'getObject' with the list of IDs/keys that this function returns.
-- NB: The order of the IDs/keys matters. This is because an object is
-- chunked. Then each chunk is stored seperatly. When one calls 'getObject'
-- the blocks retrieved is concated in the order of the IDs/keys. 
-- That means you'll get garbage if you mess up the order.
putObject ::  (Binary a) => a -> ProcessM [(Integer, NodeId)]
putObject a = do st <- getState
                 let bs = (chunkBs st) . encode $ a
                 mapM putBlock bs
-- }}}

-- {{{ getObject
-- | 'getObject' takes a list of IDs/keys that represent an object that's
-- already been put with 'putObject'.
-- NB: The order of the IDs/keys matters. This is because an object is
-- chunked. Then each chunk is stored seperatly. When one calls 'getObject'
-- the blocks retrieved is concated in the order of the IDs/keys. 
-- That means you'll get garbage if you mess up the order.
getObject ::  (Binary a) => [Integer] -> Int -> ProcessM (Maybe a)
getObject keys howMany = liftM (liftM decode) $ liftM maybeConcatBS $ mapM (\k -> getBlock k howMany) keys

-- | 'maybeConcatBS' takes '[Maybe BS.ByteString]'s and concats
-- all the bytestrings into one if none of them are Nothing.
-- Else it returns Nothing
maybeConcatBS ::  [Maybe BS.ByteString] -> Maybe BS.ByteString
maybeConcatBS blocks
  | any (== Nothing) blocks = Nothing
  | otherwise = Just . BS.concat . catMaybes $ blocks

-- }}}