{-# LANGUAGE TemplateHaskell,BangPatterns,PatternGuards,DeriveDataTypeable #-}
module Main where

-- | TODO
-- When a node never responds, it should be removed from the fingertable, maybe actively replaced?
--
-- When a node joins, it very often get it self as it's successor, that's _never_ correct for joins, only lookups to keys
-- Though this bug exists, fingerTables are never corrupted, converging takes i bit more time though
--
-- When a node joins, it makes 160 _sequenced_ lookups, these are to discover what nodes are on the net.
-- If the lookup times out, it's going to take 160*timeout for it to complete and leave 160 "Timeout" messages
-- in the logs
--
-- Most important now i gettin locking on the state. That means putting the state in a MVar and make transactions
-- when processes wants to modify it. Reads just return the current state, modify locks it, makes the modification and then opens again

import Remote.Call
import Remote.Channel
import Remote.Peer
import Remote.Process
import Remote.Init
import Remote.Encoding

import Control.Monad (liftM)
import Data.Typeable
import Control.Monad.IO.Class (liftIO)

import Control.Concurrent (threadDelay)
import qualified Data.Map as Map
import Data.List (foldl')

import Data.Digest.Pure.SHA
import Data.Binary

-- for helper debug
import qualified Data.List as List
import System.Random (randomRIO)
import Data.Ratio

--{{{ Data type and type class definitions
-- | NodeState, carries all important state variables
data NodeState = NodeState {
          self :: NodeId
        , fingerTable :: Map.Map Integer NodeId -- ^ The fingerTable
        , predecessor :: NodeId
        , timeout :: Int -- ^ The timout latency of ping
        , m :: Integer -- ^ The number of bits in a key, ususaly 160
        } deriving (Show)
instance Eq NodeState where
    (==) st1 st2 = ((self st1) == (self st2)) && 
                   ((fingerTable st1) == (fingerTable st2)) &&
                   ((predecessor st1) == (predecessor st2))
    (/=) st1 st2 = not $ (==) st1 st2


instance Binary NodeState where
  put a = do put (self a)
             put (fingerTable a)
	     put (predecessor a)
	     put (timeout a)
	     put (m a)
  get = do se <- get
           ft <- get
	   pr <- get
	   ti <- get
	   m <- get
	   return (NodeState { self = se, fingerTable = ft, predecessor = pr, timeout = ti, m=m })

successor :: NodeState -> Maybe NodeId
successor st = helper st 1 --Map.lookup 1 (fingerTable st)
    where helper st k
            | k > (m st) = Nothing
            | Just c <- Map.lookup k (fingerTable st) = Just c
            | otherwise = helper st (k+1)

cNodeId n = integerDigest . sha1 $ encode n
--}}}

-- | Shuld return the successor of US if the key asked for is in the domain (us, successor]
hasSuccessor :: NodeState -> Integer -> Maybe NodeId
hasSuccessor st key
  | Map.null (fingerTable st) = Nothing
  | otherwise = do
   let n = cNodeId (self st)
       suc = successor st
   case suc of
     Nothing -> Nothing
     (Just succ) -> if between key n ((cNodeId succ) + 1)
                    then Just succ
                    else Nothing

-- {{{ closestPrecedingNode
closestPreceding st key = do
  return $ helper st (fingerTable st) key (m st)

helper :: NodeState -> Map.Map Integer NodeId -> Integer -> Integer -> NodeId
helper st conts key 0 = self st
helper st conts key i
  | (Just hit) <- lookopAndIf c conts i = hit
  | otherwise = helper st conts key (i-1)
    where c x = between (cNodeId x) (cNodeId . self $ st) key -- c is from the fingertable


-- | Lookup a value, if a predicate on it is true, return it, else Nothing
lookopAndIf :: (Ord k) => (a -> Bool) -> Map.Map k a -> k -> Maybe a
lookopAndIf f m k
  | (Just a) <- Map.lookup k m
  , f a = Just a -- a is the node from the fingertable
  | otherwise = Nothing
-- }}}

-- | is n in the domain of (a, b) ?
between :: Integer -> Integer -> Integer -> Bool
between n a b
  | a == b = n /= a --error "n can't be between a and b when a == b" -- can't be alike
  | (a < b) = (a < n) && (n < b)
  | (b < a) = not $ between n (b-1) (a+1)

-- {{{ addFinger
-- | Adds a finger to the fingertable. If there already exists a finger they are compared to see who's the best fit.
addFinger :: NodeId -> NodeState -> NodeState
addFinger newFinger st = st {fingerTable = foldl' pred (fingerTable st) [1..(m st)]}
    where pred ft i
            | Just prevFinger <- Map.lookup i ft -- there exists a node in the fingertable, is the new on ecloser?
            , let fv = fingerVal st i in (between c fv (cNodeId prevFinger)) && (newFinger /= (self st)) && (between c fv n)
            = Map.insert i newFinger ft
            | Nothing <- Map.lookup i ft -- there is no node, we just put it in if it fits
            , let fv = fingerVal st i in (newFinger /= (self st)) && (between c fv n)
            = Map.insert i newFinger ft
            | otherwise = ft

          c = cNodeId newFinger
          n = cNodeId (self st)

fingerVal ::  (Integral a) => NodeState -> a -> Integer
fingerVal st k = mod ((cNodeId . self $ st) + 2^(k-1)) (2^(m st))
-- }}}

-- {{{ State stuff
data PassState = GetState ProcessId | PutState NodeState | RetState NodeState deriving (Show, Typeable)

instance Binary PassState where
  put (GetState pid) = do put (0 :: Word8)
                          put pid
  put (PutState i) = do put (1 :: Word8)
                        put i
  put (RetState i) = do put (2 :: Word8)
                        put i
  get = do
        flag <- getWord8
        case flag of
          0 -> do
               pid <- get
               return (GetState pid)
          1 -> do
               i <- get
               return (PutState i)
          2 -> do
               i <- get
               return (RetState i)

getState :: ProcessM NodeState
getState = do nodeId <- getSelfNode
              let process = ProcessId nodeId 7 -- THIS SEEMS TO BE THE MAGICAL NUMBER, it means that right now, CloudHaskell spawns 6 processes to handle all the internal stuff, that means the first process i spawn myself is number seven. This one holds the state.
              pid <- getSelfPid
              send process (GetState pid)
              (RetState a) <- expect
              return a

putState :: NodeState -> ProcessM ()
putState st = do nodeId <- getSelfNode
                 let process = ProcessId nodeId 7
                 send process (PutState st)
-- }}}

-- | someone asks you for a successor, if you know it you reply to the original caller,
-- | else you relay the query forward
relayFndSucc :: NodeId -> ProcessId -> Integer -> ProcessM ()
relayFndSucc nid caller key = do
  st' <- getState
  let st = addFinger (nodeFromPid caller) (addFinger nid st')
      x = 2^(m st) :: Integer
      fm :: Integer -> Double
      fm = fromRational . (% x)
      sh :: Integer -> String
      sh = (take 5) . show
  putState st
  case (hasSuccessor st key) of
      (Just suc) -> do 
             --say ((sh . fm . cNodeId . self $ st) ++ " hasSucc: " ++ (sh . fm $ key) ++ " = " ++ (sh . fm . cNodeId $ suc))
             send caller (suc, key) -- If we only are two in the ring, we will send ourselves
      _ -> do
          recv <- closestPreceding st key -- | find the next to relay to
          case recv == (nodeFromPid caller) of
            False -> do case recv == (self st) of
                          False -> do
                            let clos = $( mkClosureRec 'relayFndSucc )
                            spawn recv (clos (self st) caller key)
	                    return ()
                          True -> do
                            send caller (self st)
            True -> do self <- getSelfNode
                       --say $ "Circle: " ++ (show recv)
                       send caller self -- We've detected a circle, we cant say NodeA's sucessor is NodeA
                       return ()

getPred = do st <- getState
             return (predecessor st)

-- | notifier is telling you he thinks he is your predecessor, check if it's true.
notify notifier = do
  st <- getState
  if between (cNodeId notifier) (cNodeId . predecessor $ st) (cNodeId . self $ st)
    then putState $ st {predecessor = notifier}
    else return ()

$( remotable ['relayFndSucc, 'getPred, 'notify] )


-- | Joins a chord ring. Takes the id of a known node to bootstrap from.
joinChord :: NodeId -> ProcessM ()
joinChord node = do
    st <- getState
    succ <- remoteFindSuccessor node (mod ((cNodeId . self $ st) + 1) (m $ st))
    say $ "Ret self?: " ++ (show (fst succ == (self st))) ++ " Ret boot?: " ++ (show (fst succ == node))
    buildFingers (fst succ)
    sst <- getState
    say $ "Finish join: " ++ (show . nils . fingerTable $ sst)
    let suc = successor sst
    case suc of
      (Just c) -> spawn c (notify__closure (self st)) >> return ()
      Nothing -> return ()

nils :: Map.Map Integer NodeId -> [NodeId]
nils = (List.map (\x -> head x)) . List.group . List.sort . Map.elems -- TODO this is a debug function

-- | This is run periodically to check if our fingertable is correct
stabilize = do
  liftIO $ threadDelay 5000000 -- 5 sec
  st <- getState
  --say $ "Start stab: " ++ (show . nils . fingerTable $ st)
  case successor st of
    (Just succ) -> do succPred <- callRemote succ getPred__closure
                      if between (cNodeId succPred) (cNodeId . self $ st) (cNodeId succ)
                        then do st' <- getState
                                putState (addFinger succPred st')
                                spawn succ (notify__closure (self st'))
                                say ("New succ: " ++ (show succPred)) >> stabilize
                        else spawn succ (notify__closure (self st)) >> stabilize
    Nothing -> stabilize

-- | This is a debug function, it periodically requests to know the sucessor of a random key in the ring
randomFinds = do
  liftIO $ threadDelay 8000000 -- 4 sec
  st <- getState
  key <- liftIO $ randomRIO (1, 2^(m st)) :: ProcessM Integer
  (succ, k) <- findSuccessor key
  let x = 2^(m $ st) :: Integer
      fm :: Integer -> Double
      fm = fromRational . (% x)
      sh = (take 5) . show
  say $ (sh . fm . cNodeId . self $ st) ++ " says succ " ++ (sh . fm $ key) ++ " is " ++ (sh . fm . cNodeId $ succ) ++ " " ++ (show $ key == k)
  randomFinds


-- | YOU are wordering who's the successor of a certain key, if you don't know yourself
-- | you relay it forward with YOU as the original caller.
findSuccessor :: Integer -> ProcessM (NodeId, Integer)
findSuccessor key = do
  st <- getState
  case (hasSuccessor st key) of
      (Just suc) -> return (suc, key)
      _ -> do
          selfPid <- getSelfPid -- ^ get your pid
          recv <- closestPreceding st key -- | find the next to relay to
          case recv == (self st) of
            False -> do ret <- remoteFindSuccessor recv key
                        return ret
            True -> say "Find succ should not be here" >> liftIO (threadDelay 5000000) >> findSuccessor key

remoteFindSuccessor :: NodeId -> Integer -> ProcessM (NodeId, Integer)
remoteFindSuccessor node key = do
  st <- getState
  selfPid <- getSelfPid
  spawn node (relayFndSucc__closure (self st) selfPid (key :: Integer))
  succ <- receiveTimeout 10000000 [match (\x -> return x)] :: ProcessM (Maybe (NodeId, Integer)) -- ^ TODO should time out and retry
  case succ of
    Nothing -> say "Timed out, retrying" >> remoteFindSuccessor node (key :: Integer)
    Just c -> do
                st' <- getState
                let uSt = addFinger (fst c) st'
                putState uSt
                return c

-- {{{ buildFingers
buildFingers :: NodeId -> ProcessM ()
buildFingers buildNode = do
                      st <- getState
                      nodeId <- getSelfNode
                      let f = remoteFindSuccessor buildNode
                          nodids = map (fingerVal st) r
                          r = [1 .. (m $ st)]
                      fingers <- sequence $ map f nodids
                      return ()
-- }}}

bootStrap st _ = do
  selfN <- getSelfNode
  let st' = st { self = selfN, predecessor = selfN }
  peers <- getPeers
  let peers' = findPeerByRole peers "NODE"
  case length peers' > 1 of
    True -> do
             spawnLocal (joinChord (head . (drop 1) $ peers'))
             spawnLocal stabilize
             spawnLocal randomFinds
             handleState st'
    False -> do spawnLocal stabilize
                spawnLocal randomFinds
                handleState (addFinger (self st') st')

-- | handlet get and puts for the state
handleState st = do
  pid <- getSelfPid
  updSt <- receiveWait (map match [hsGet])
  handleState updSt
  where hsGet (GetState pid) = send pid (RetState st) >> return st
        hsGet (PutState nSt) = return nSt

main = remoteInit Nothing [Main.__remoteCallMetaData] (bootStrap initState)

initState = NodeState {
          self = undefined
        , fingerTable = Map.empty -- ^ The fingerTable
        , predecessor = undefined
        , timeout = 10 -- ^ The timout latency of ping
        , m = 160 -- ^ The number of bits in a key, ususaly 160
        }
