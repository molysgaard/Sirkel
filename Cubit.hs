{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternGuards #-}
import Remote.Call
import Remote.Channel
import Remote.Peer
import Remote.Process
import Remote.Init
import Remote.Encoding
import Remote.Reg

import Data.Typeable
import Data.Binary

import qualified Data.Set as Set

import Control.Concurrent (threadDelay)
import Control.Monad (liftM, filterM)
import Control.Monad.IO.Class (liftIO)
import System.Random (randomRIO)
import Data.List (sortBy)

type Keyword = String
type KeywordSet = Set.Set Keyword

type NodeSet = Set.Set CubitId

type LeafSet = NodeSet

type RingMembers = NodeSet
type RingCandidates = NodeSet

type Ring = (RingMembers, RingCandidates)
type Rings = [Ring]

type NList = [CubitId]

type CubitId = (Keyword, NodeId)

-- {{{ CubitState
data CubitState = CubitState
    { self :: CubitId
    , fanOut :: Int
    , nmin :: Int
    , perb :: Double
    , rings :: Rings
    } deriving (Eq, Ord, Read, Show, Typeable)

instance Binary CubitState where
  put cs = put (self cs) >> put (fanOut cs) >> put (nmin cs) >> put (perb cs) >> put (rings cs)
  get = do self <- get
           fo <- get
           nm <- get
           perb <- get
           rings <- get
           return $ CubitState
             { self = self
             , fanOut = fo
             , nmin = nm
             , perb = perb
             , rings = rings
             }
-- }}}

nodeID :: CubitId -> Keyword
nodeID = fst

editDistance a b = length a + length b
dist n kw = editDistance (nodeID n) kw

ringNodes ::  Rings -> NList
ringNodes = concat . (map (Set.elems . fst))

selectRandom :: NodeSet -> Double -> IO NodeSet
selectRandom set val = setFilterM (pred val) set
  where pred :: Double -> t -> IO Bool
        pred n  _ = randomRIO (0, 1) >>= return . (\x -> n < x)

setFilterM :: (Ord a, Monad m) => (a -> m Bool) -> Set.Set a -> m (Set.Set a)
setFilterM p set = liftM Set.fromList (filterM p (Set.elems set))

rankNodes :: [CubitId] -> Keyword -> [CubitId]
rankNodes ns kw = sortBy (compNodes kw) ns

compNodes :: Keyword -> CubitId -> CubitId -> Ordering
compNodes kw a b
  | ed a < ed b = LT
  | ed a == ed b = EQ
  | ed a > ed b = GT
    where ed n = editDistance kw (nodeID n)

remExt ::  (Eq a) => [a] -> [a] -> [a]
remExt [] _ = []
remExt (a:as) bs
  | a `elem` bs = remExt as bs
  | otherwise = a : remExt as bs

-- {{{ search
search ::  Keyword -> ProcessM NList
search kw = do
    st <- getState
    search' kw (nmin st) (fanOut st) (perb st) [self st] [] []

search' :: Keyword -> Int -> Int -> Double -> NList -> NList -> NList -> ProcessM NList
search' kw nmin fanOut perb pending checked failed
  | nods@(n:ns) <- let q = fromIntegral (length kw) * perb
                       pred p = fromIntegral (editDistance (nodeID p) kw) < q
                              || dist p kw < dist (last (take nmin (rankNodes checked kw))) kw
                   in filter pred pending
  , length nods < fanOut
  = do flag <- ptry $ getClosestNodes kw n :: ProcessM (Either TransmitException NList)
       case flag of
         Left _ -> search' kw nmin fanOut perb ns checked (n:failed)
         Right ret' -> do
           let ret = remExt ret' (failed ++ checked)
               chk = n:checked
               pend = ret ++ pending
           search' kw nmin fanOut perb pend chk failed
  | otherwise = return pending
-- }}}

getClosestNodes :: Keyword -> CubitId -> ProcessM NList
getClosestNodes kw sender = do
    st <- getState
    return $ take (nmin st) $ rankNodes (ringNodes (rings st)) kw

-- {{{ State stuff
data PassState = ReadState ProcessId
               | RetReadState CubitState
               | TakeState ProcessId
               | RetTakeState CubitState
               | PutState CubitState deriving (Show, Typeable)

instance Binary PassState where
  put (ReadState pid) = do put (0 :: Word8)
                           put pid
  put (RetReadState i) = do put (1 :: Word8)
                            put i

  put (TakeState pid) = do put (2 :: Word8)
                           put pid
  put (RetTakeState i) = do put (3 :: Word8)
                            put i
  put (PutState i) = do put (4 :: Word8)
                        put i
  get = do
        flag <- getWord8
        case flag of
          0 -> do
               pid <- get
               return (ReadState pid)
          1 -> do
               i <- get
               return (RetReadState i)
          2 -> do
               pid <- get
               return (TakeState pid)
          3 -> do
               i <- get
               return (RetTakeState i)
          4 -> do
               i <- get
               return (PutState i)

getState :: ProcessM CubitState
getState = do statePid <- getStatePid
              pid <- getSelfPid
              send statePid (ReadState pid)
              ret <- receiveTimeout 10000000 [ match (\(RetReadState st) -> return st) ]
              case ret of
                Nothing -> say "asked for state but state process did not return within timeout, retrying" >> getState
                Just st -> return st

modifyState :: (CubitState -> CubitState) -> ProcessM CubitState
modifyState f = do
                 statePid <- getStatePid
                 selfPid <- getSelfPid
                 send statePid (TakeState selfPid)
                 ret <- receiveTimeout 10000000 [ match (\(RetTakeState st) -> return st) ]
                 case ret of
                   Nothing -> say "asked for modify, timeout, retrying" >> liftIO (threadDelay 50000000) >> modifyState f
                   Just st -> send statePid (PutState (f st)) >> return (f st)

getStatePid :: ProcessM ProcessId
getStatePid = do nid <- getSelfNode
                 statePid <- nameQuery nid "CUBIT-STATE"
                 case statePid of
                   Nothing -> say "State not initialized, state-process is not running" >> getStatePid
                   Just pid -> return pid

-- {{{ handleState
-- | handlet get and puts for the state
-- this function is butt ugly and needs some hefty sugar
handleState st' = do
  nameSet "CUBIT-STATE"
  loop st'

  where loop :: CubitState -> ProcessM ()
        loop st = do
            receiveWait
              [ matchIf (\x -> case x of
                                 (ReadState _) -> True
                                 _ -> False) (\(ReadState pid) -> getSt st pid)
              , matchIf (\x -> case x of
                               (TakeState _) -> True
                               _ -> False) (\(TakeState pid) -> modSt st pid) ]
            >>= loop
        getSt st pid = do
          send pid (RetReadState st)
          return st
        modSt st pid = do
          send pid (RetTakeState st)
          ret <- receiveTimeout 1000000 [ matchIf (\x -> case x of
                                                           (PutState _) -> True
                                                           _ -> False)  (\(PutState st) -> return st) ]
          case ret of
            Nothing -> say "process asked for modify, but did not return new state" >> return st
            Just newSt -> return newSt
-- }}}
-- }}}

$( remotable ['getClosestNodes] )
