{-# LANGUAGE PatternGuards #-}
module DataTypes where

import Data.Word
import qualified Data.Map as Map
import Data.Binary
import Control.Monad
import Network.Socket
import qualified Control.Monad.State as St
import System.Random(StdGen)
import Control.Concurrent.MVar
import Text.Printf
import Data.Maybe (fromJust)

import Remote.Process

--- {{{ Kademila Data types
type Key = Integer

type Contact = NodeId

data ChordMessage = ChordMessage Key Contact ChordParams deriving (Eq, Show)-- ^ The msgId Sender and params
instance Binary ChordMessage where
    put (ChordMessage k c p) = do
                                put k
                                put c
                                put p
    get = do
            return ChordMessage `ap` get `ap` get `ap` get

data ChordParams = FndSuc Key | FndRsp Contact | Ping | Pong | Notify | GetPred | PredRsp Contact | ChordError String deriving (Eq, Show)
instance Binary ChordParams where
    put (FndSuc k) = do
                      put (0 :: Word8)
                      put k
    put (FndRsp c) = do
                      put (1 :: Word8)
                      put c
    put Ping = do
                      put (2 :: Word8)
    put Notify = do
                      put (3 :: Word8)
    put (ChordError str) = do
                      put (4 :: Word8)
                      put str
 
    get = do
            tag <- getWord8
            case tag of
                0 -> do
                       k <- get
                       return (FndSuc k)
                1 -> do
                       c <- get
                       return (FndRsp c)
                2 -> do
                       return Ping
                3 -> do
                       return Notify
                4 -> do
                       err <- get
                       return (ChordError err)

-- | NodeState, carries all important state variables
data NodeState = NodeState {
          self :: Contact
        , fingerTable :: Map.Map Integer Contact -- ^ The fingerTable
        , predecessor :: Contact
        , timeout :: Int -- ^ The timout latency of ping
        , m :: Int -- ^ The number of bits in a key, ususaly 160
        , alpha :: Int -- ^ The number of parralell queries
        , bootstrapNode :: Contact -- ^ A node in the network
        } deriving (Show)
instance Eq NodeState where
    (==) st1 st2 = ((self st1) == (self st2)) && 
                   ((fingerTable st1) == (fingerTable st2)) &&
                   ((predecessor st1) == (predecessor st2))
    (/=) st1 st2 = not $ (==) st1 st2

successor :: NodeState -> Maybe Contact
successor st = helper st 1
    where helper st k
            | fromIntegral k > (m st) = Nothing
            | Just c <- Map.lookup k (fingerTable st) = Just c
            | otherwise = helper st (k+1)
