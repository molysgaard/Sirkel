{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternGuards #-}

module Cubit where

import Remote.Call
import Remote.Channel
import Remote.Peer
import Remote.Process
import Remote.Init
import Remote.Encoding
import Remote.Reg

import Data.Typeable
import Data.Binary
import Data.Maybe (fromJust, catMaybes)

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List

import Control.Concurrent (threadDelay)
import Control.Monad (liftM, filterM, foldM)
import Control.Monad.IO.Class (liftIO)
import System.Random (randomRIO)
import Data.List (sortBy)

type Keyword = String
type KeywordSet = Set.Set Keyword

type ObjectRef = [Integer]
type ObjectRefs = Set.Set ObjectRef

type NodeSet = Set.Set CubitId

type LeafSet = NodeSet

type RingMembers = NodeSet
type RingCandidates = NodeSet

type Ring = (RingMembers, RingCandidates)
type Rings = Map.Map Int Ring

type NList = [CubitId]

type CubitId = (Keyword, NodeId)

-- {{{ CubitState
data CubitState = CubitState
    { self :: CubitId
    , fanOut :: Int
    , perb :: Double
    , kring :: Int
    , rings :: Rings
    , frepl :: Int
    , leafSet :: LeafSet
    , gossipTime :: Int
    , replaceTime :: Int
    } deriving (Eq, Ord, Read, Show, Typeable)

instance Binary CubitState where
  put cs = put (self cs) >> put (fanOut cs) >> put (perb cs) >> put (kring cs) >> put (rings cs) >> put (frepl cs) >> put (leafSet cs) >> put (gossipTime cs) >> put (replaceTime cs)
  get = do self <- get
           fo <- get
           perb <- get
           kring <- get
           rings <- get
           frepl <- get
           leafSet <- get
           gossipTime <- get
           replaceTime <- get
           return $ CubitState
             { self = self
             , fanOut = fo
             , perb = perb
             , kring = kring
             , rings = rings
             , frepl = frepl
             , leafSet = leafSet
             , gossipTime = gossipTime
             , replaceTime = replaceTime
             }
-- }}}

nodeID :: CubitId -> Keyword
nodeID = fst

nodeAddr :: CubitId -> NodeId
nodeAddr = snd

editDistance :: Eq a => [a] -> [a] -> Int
editDistance a b 
    = last (if lab == 0 then mainDiag
	    else if lab > 0 then lowers !! (lab - 1)
		 else{- < 0 -}   uppers !! (-1 - lab))
    where mainDiag = oneDiag a b (head uppers) (-1 : head lowers)
	  uppers = eachDiag a b (mainDiag : uppers) -- upper diagonals
	  lowers = eachDiag b a (mainDiag : lowers) -- lower diagonals
	  eachDiag a [] diags = []
	  eachDiag a (bch:bs) (lastDiag:diags) = oneDiag a bs nextDiag lastDiag : eachDiag a bs diags
	      where nextDiag = head (tail diags)
	  oneDiag a b diagAbove diagBelow = thisdiag
	      where doDiag [] b nw n w = []
		    doDiag a [] nw n w = []
		    doDiag (ach:as) (bch:bs) nw n w = me : (doDiag as bs me (tail n) (tail w))
			where me = if ach == bch then nw else 1 + min3 (head w) nw (head n)
		    firstelt = 1 + head diagBelow
		    thisdiag = firstelt : doDiag a b firstelt diagAbove (tail diagBelow)
	  lab = length a - length b
          min3 x y z = if x < y then x else min y z

dist ::  CubitId -> Keyword -> Int
dist n kw = editDistance (nodeID n) kw

nodeDist ::  CubitId -> CubitId -> Int
nodeDist n m = editDistance (nodeID n) (nodeID m)

ringNodes :: Rings -> NodeSet
ringNodes = (Map.fold Set.union Set.empty) . (Map.map fst)

selectRandom :: Double -> NodeSet -> IO NodeSet
selectRandom val set = setFilterM (pred val) set
  where pred :: Double -> t -> IO Bool
        pred n  _ = randomRIO (0, 1) >>= return . (\x -> n < x)

setFilterM :: (Ord a, Monad m) => (a -> m Bool) -> Set.Set a -> m (Set.Set a)
setFilterM p set = liftM Set.fromList (filterM p (Set.elems set))

setMapM :: (Monad m, Ord a, Ord b) => (a -> m b) -> Set.Set a -> m (Set.Set b)
setMapM f set = liftM Set.fromList (mapM f (Set.elems set))

setMapM_ f set = mapM f (Set.elems set)


mapMapWithKeyM :: (Monad m, Ord k, Functor m) =>(k -> t -> m a) -> Map.Map k t -> m (Map.Map k a)
mapMapWithKeyM f' = fmap Map.fromList . (mapM (p f')) . Map.toList
  where p f (k, v) = do r <- f k v
                        return (k, r)

setFoldM :: (Monad m, Ord a, Ord b) => (a -> b -> m a) -> a -> Set.Set b -> m a
setFoldM f v set = foldM f v (Set.elems set)

setCatMaybes = Set.fromList . catMaybes . Set.toList

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

getVolume :: NodeSet -> Int
getVolume ns = sum [nodeDist n m | n <- Set.elems ns, m <- Set.elems ns]



addNodes :: NodeSet -> CubitState -> CubitState
addNodes ns st = Set.fold addNode st ns

addNode :: CubitId -> CubitState -> CubitState
addNode n st = st {rings = addToRings (self st) n (kring st) 4 (rings st)}

addToRings :: CubitId-> CubitId-> Int-> Int-> Map.Map Int (NodeSet, NodeSet)-> Map.Map Int (NodeSet, NodeSet)
addToRings self n k l rs = let d = nodeDist self n
                           in Map.alter (addToRing self n k l) d rs

-- tar ikke hensyn til polytop enda
addToRing :: (Ord a) =>a-> a-> Int-> Int-> Maybe (Set.Set a, Set.Set a)-> Maybe (Set.Set a, Set.Set a)
addToRing self n _ _ Nothing
  | n /= self
  = Just (Set.singleton n, Set.empty)
  | otherwise = Nothing
addToRing self n k l (Just (membs, cands))
  | Set.size membs < k
  , n /= self
  = Just (Set.insert n membs, cands)
  | Set.size cands < l
  , n /= self
  = Just (membs, Set.insert n cands)
  | otherwise = Just (membs, cands)

getNodeId :: ProcessM CubitId
getNodeId = getState >>= return . self

getClosestNodes :: Keyword -> CubitId -> ProcessM NList
getClosestNodes kw sender = do
    st <- modifyState (addNode sender)
    return $ take (fanOut st) $ rankNodes (Set.elems $ ringNodes (rings st)) kw

getRandomNodes :: Int -> ProcessM NodeSet
getRandomNodes k = do
    st <- getState
    let ns' = ringNodes (rings st)
        ratio = (fromIntegral k) / (fromIntegral (Set.size ns'))
    liftIO $ selectRandom ratio ns'

isOwner st kw
  | head (rankNodes (Set.elems set) kw) == self st = True
  | otherwise = False
  where set = Set.insert (self st) (leafSet st)

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

-- {{{ gossip
gossipRequest :: NodeSet -> ProcessM NodeSet
gossipRequest newNodes = do
    st <- getState
    modifyState (addNodes newNodes)
    ns <- liftIO $ selectRandom 0.3 (ringNodes (rings st))
    return ns

$( remotable ['getClosestNodes, 'gossipRequest, 'getRandomNodes, 'getNodeId] )

-- {{{ search
initSearch ::  Keyword -> ProcessM NList
initSearch kw = do
    st <- getState
    search (self st) kw (fanOut st) (perb st) [self st] [] []

search :: CubitId -> Keyword -> Int -> Double -> NList -> NList -> NList -> ProcessM NList
search self kw fanOut perb pending checked failed
  | nods@(n:ns) <- let q = fromIntegral (length kw) * perb
                       pred p =  fromIntegral (editDistance (nodeID p) kw) <= q
                              || null checked
                              || dist p kw < dist (last (take fanOut (rankNodes checked kw))) kw
                   in filter pred pending
  , length nods < fanOut
  , null nods == False
  = do flag <- ptry $ callRemote (nodeAddr n) (getClosestNodes__closure kw self) :: ProcessM (Either TransmitException NList)
       case flag of
         Left _ -> search self kw fanOut perb ns checked (n:failed)
         Right ret' -> do
           let chk = n:checked
               ret = remExt ret' (failed ++ chk)
               pend = ret ++ ns
           --say $ (show chk) ++ " " ++ (show ret) ++ " " ++ (show pend)
           search self kw fanOut perb pend chk failed
  | otherwise = return $ rankNodes checked kw
-- }}}

scheduleGossip st = liftIO (threadDelay (gossipTime st)) >> gossip >> say "gossip" >> scheduleGossip st

gossip :: ProcessM CubitState
gossip = do
    st <- getState
    ns <- liftIO $ selectRandom 0.3 (ringNodes (rings st)) :: ProcessM NodeSet
    newNodes <- setFoldM (\acc n -> fmap (Set.union acc) (callRemote (nodeAddr n) (gossipRequest__closure ns))) Set.empty ns
    modifyState (addNodes newNodes)
-- }}}

-- {{{
join :: [CubitId] -> [CubitId] -> Int -> ProcessM CubitState
join pend checked 0 = say (show (pend ++ checked)) >> modifyState (addNodes (Set.fromList (pend ++ checked)))
join [] c _ = modifyState (addNodes (Set.fromList c))
join (p:pend) checked k = do
    st <- getState
    ns' <- callRemote (nodeAddr p) (getRandomNodes__closure (kring st))
    join ((Set.elems ns') ++ pend) (p:checked) (k - 1)
-- }}}

scheduleReplace st = liftIO (threadDelay (replaceTime st)) >> say "replace" >> replace >> scheduleReplace st

-- {{{ replace
-- TODO FIXME denne tar ikke hensyn til at rings kan være null!
replace ::  ProcessM CubitState
replace = do
  st <- getState
  n <- liftIO $ randomRIO (0,(length . Map.toList $ rings st) - 1)
  let ring = (\s -> Set.union (fst s) (snd s)) . snd . (!! n) . Map.toList $ (rings st)
  modifyState (\x -> x {rings = Map.insert n (vol (st, ring, Set.empty)) (rings st)})

vol :: (CubitState, NodeSet, NodeSet) -> (NodeSet, NodeSet)
vol (st, a, b)
  | Set.size a > kring st = vol (tiss st a a Nothing b 0)
  | otherwise = (a, b)

tiss :: CubitState -> NodeSet -> NodeSet -> Maybe CubitId -> NodeSet -> Int -> (CubitState, NodeSet, NodeSet)
tiss st as a m b v
  | Set.null a
  , m /= Nothing = (st, Set.delete (fromJust m) a, Set.insert (fromJust m) b)
  | m == Nothing || s > v
  = tiss st (Set.delete n as) a (Just n) b s
  | otherwise = tiss st as a m b v
  where s = getVolume(Set.delete n a)
        n = Set.findMin as
-- }}}

-- {{{ replicate
replicate :: ProcessM ()
replicate = do
  st <- getState
  let ls = Set.insert (self st) (leafSet st)
  return ()
-- }}}

-- {{{ Datatypes
-- | Datatype encapsulating the things we can do with the HashTable
data KeywordStore = Insert String ObjectRefs | Lookup Keyword ProcessId | Delete Keyword | Janitor deriving (Eq, Show, Typeable)
instance Binary KeywordStore where
  put (Insert kw objs) = do
                      put (0 :: Word8)
                      put kw
                      put objs
  put (Lookup kw pid) = do
                      put (1 :: Word8)
                      put kw
                      put pid
  put (Delete kw) = do
                      put (2 :: Word8)
                      put kw
  put Janitor = put (3 :: Word8)
  get = do flag <- getWord8
           case flag of
             0 -> do kw <- get
                     objs <- get
                     return $ Insert kw objs
             1 -> do key <- get
                     pid <- get
                     return $ Lookup key pid
             2 -> do key <- get
                     return $ Delete key
             3 -> return Janitor

type KeywordTable = Map.Map Keyword (Bool, ObjectRefs)
-- }}}

data RetObj = LookupError | ObjFound ObjectRefs deriving (Show, Typeable)
instance Binary RetObj where
  put LookupError = put (0 :: Word8)
  put (ObjFound obj) = put (1 :: Word8) >> put obj
  get = do flag <- getWord8
           case flag of
             0 -> return LookupError
             1 -> do bs <- get
                     return $ ObjFound bs

-- {{{ putObject, puts a block, returns the successor of that block. You will
-- also find the block replicated on the (r st) next nodes, but it is the node
-- responsible for the block that is responsible for delivering the block to them
putObject :: Keyword -> ObjectRefs -> ProcessM NodeId
putObject key objs = do
    succs <- initSearch key
    putObject' key objs (nodeAddr . head $ succs)

-- | putObject' put a block on a node we know
putObject' :: Keyword -> ObjectRefs -> NodeId -> ProcessM NodeId
putObject' key objs succ = do
    ret <- getKeywordPid succ
    case ret of
      Just pid -> do
          flag <- ptry $ send pid (Insert key objs) :: ProcessM (Either TransmitException ())
          case flag of
            Left _ -> say "put block failed, retrying" >> (liftIO (threadDelay 5000000)) >> putObject key objs
            Right _ -> return succ
      Nothing -> say "put block failed, retrying" >> (liftIO (threadDelay 5000000)) >> putObject key objs
-- }}}

-- {{{ getKeywordPid
getKeywordPid :: NodeId -> ProcessM (Maybe ProcessId)
getKeywordPid node = do 
                 statePid <- ptry $ nameQuery node "DHASH-BLOCK-STORE" :: ProcessM (Either ServiceException (Maybe ProcessId))
                 case statePid of
                   Right (Just pid) -> return (Just pid)
                   _ -> say "Dhash block store not initialized, state-process is not running" >> return Nothing
-- }}}

-- {{{ sendObject
-- | sendObject is a function to send a block from a lookup in the HashTable.
-- We do this in a separate thread because we don't want to block lookups etc.
-- while we are sending.
-- TODO there have to be some sort of queue here in the future, to limit the
-- upload
sendObject :: Maybe (Bool, ObjectRefs) -> ProcessId -> ProcessM ()
sendObject Nothing pid = do
    ptry (send pid LookupError) :: ProcessM (Either TransmitException ())
    return ()
sendObject (Just (_, bs)) pid = do
    ptry (send pid (ObjFound bs)) :: ProcessM (Either TransmitException ())
    return ()
-- }}}

-- {{{ initBlockStore
-- | initBlockStore starts the BlockStore and handles requests to
-- insert, lookup and delete blocks as well as the janitor process
-- to check if ownership of any block has changed
initBlockStore :: KeywordTable -> ProcessM ()
initBlockStore ht' = do
  nameSet "DHASH-BLOCK-STORE"
  spawnLocal janitorSceduler
  loop ht'
  where loop :: KeywordTable -> ProcessM ()
        loop ht = do
            newHt <- receiveWait
              [ matchIf (\x -> case x of
                                 (Insert _ _) -> True
                                 _ -> False)
                        (\(Insert kw val) -> insertBlock ht kw val)
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
lookupBlock :: Keyword -> ProcessId -> KeywordTable -> ProcessM KeywordTable
lookupBlock kw pid ht = do let answ = Map.lookup kw ht
                           spawnLocal (sendObject answ pid)
                           return ht
-- }}}

-- {{{ removeBlock
removeBlock :: KeywordTable -> Keyword -> ProcessM KeywordTable
removeBlock ht key = do 
    st <- getState
    -- if we are the owner of the block, also send delete
    -- to all the replicas
    -- else just delete our copy
    if isOwner st key
      then do let ht' = Map.delete key ht
              bs <- liftM setCatMaybes $ setMapM (getKeywordPid . nodeAddr) (leafSet st)
              say "deleting replicas"
              setMapM_ ((flip send) (Delete key)) bs
              return ht
      else return (Map.delete key ht)
-- }}}

-- {{{ insertBlock
insertBlock :: KeywordTable -> Keyword -> ObjectRefs -> ProcessM KeywordTable
insertBlock ht key val = do 
  st <- getState
  -- if we are the right owner of this block
  -- or if we are just replicating
  -- TODO would be smart to check if we should be
  -- replicating but it is not trivial without a predecessor list
  -- wich is not implemented at this time
  if isOwner st key
    then do setMapM_ (\n -> putObject' key val (nodeAddr n)) (leafSet st)
            return $ Map.alter (updSet True val) key ht
    else do say "replicating"
            return $ Map.alter (updSet False val) key ht
  where updSet :: Bool -> ObjectRefs -> Maybe (Bool, ObjectRefs) -> Maybe (Bool, ObjectRefs)
        updSet own new Nothing = Just (own, new)
        updSet own new (Just (_, old)) = Just (own, Set.union new old)
-- }}}

-- {{{ janitor
-- | janitor takes the KeywordTable and checks if the ownership of blocks
-- has changed sice last time. If so it updates replication etc.
janitor :: KeywordTable -> ProcessM KeywordTable
janitor ht = do st <- getState
                mapMapWithKeyM (fix st) ht
-- }}}

-- {{{ janitorSceduler
-- | janitorSceduler is a process that periodically sends a "janitor"
-- message to the block manager, this because we don't have MVar etc.
janitorSceduler :: ProcessM ()
janitorSceduler = do
         self <- getSelfNode
         ret <- getKeywordPid self
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
fix :: CubitState -> Keyword -> (Bool, ObjectRefs) -> ProcessM (Bool, ObjectRefs)
fix st key entry@(True, bs)
  | isOwner st key
  = return entry
  | otherwise = do 
             say "we are no longer responsible for this block"
             putObject key bs
             return (False,bs)

fix st key entry@(False, bs)
  | isOwner st key
  = do 
      say "we are the new block owner"
      setMapM_  (\n -> putObject' key bs (nodeAddr n)) (leafSet st)
      return (True,bs)
  | otherwise = return entry
-- }}}
