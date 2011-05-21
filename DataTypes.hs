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
import Remote.Channel

--- {{{ Kademila Data types


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
