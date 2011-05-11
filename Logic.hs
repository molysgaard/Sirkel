{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
module Logic where

import Control.Concurrent
import Data.Maybe
import System.IO
import Network
import DataTypes
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BS.Char8
import qualified Data.Binary as Bin
import qualified Data.Map as Map
import Control.Monad
import Control.Monad.State
import Control.Exception

cNodeId = id

type NodeId = Int

--- {{{ findSuccessor
--- {{{ findSuccessor
-- | Asks a node n for the successor of id
findSuccessor ::  NodeState -> NodeId -> IO (Either String Contact)
findSuccessor st id 
  | (Just suc) <- successor st = do
                         let n = cNodeId (self st)
                         if ((n < id) && (id <= (cNodeId suc)))
                             then return (Right suc)
                             else do
                                    let reciever = closestPrecedingNode st id
                                    case reciever == suc of
                                        True -> return (Right reciever)
                                        False -> remoteFindSuccessor st reciever id
  | otherwise = return $ Left "No fingers"
  -- | otherwise = return $ Right (self st)
--- }}}

-- {{{ addFinger
addFinger c st = st {fingerTable = foldl pred (fingerTable st) [1..(fromIntegral $ m st)]}
    where pred a b
            | (gt b) && (lt b) = Map.insert b c a
            | otherwise = a
          gt b = ((cNodeId c) > (fingerVal st b)) || ((cNodeId c) < (cNodeId . self $ st))
          lt b
           | Just cur <- Map.lookup b (fingerTable st) = (cNodeId c) <= (cNodeId cur) 
           | otherwise = True
fingerVal ::  (Integral a) => NodeState -> a -> NodeId
fingerVal st k = mod ((cNodeId . self $ st) + 2^(k-1)) (2^(fromIntegral $ m st))
-- }}}

-- {{{ stabilize
stabilize st = do
        (ChordMessage _ _ (PredRsp c)) <- getPred st
        notify (fromJust . successor $ (stab c)) (stab c)
        return (stab c)
    where stab c
            | (cNodeId . self $ st) < (cNodeId c) && (cNodeId c) < (cNodeId . fromJust . successor $ st) = st {fingerTable = newFingers c}
            | otherwise = st
          newFingers c = Map.insert 1 c (fingerTable st)
-- }}}

-- {{{ join
join bootstrap st = do
                        let newSt = addFinger bootstrap st
                        c <- remoteFindSuccessor newSt bootstrap (cNodeId (self newSt))
                        case c of 
                          (Right s) -> do
                                newSt <- buildFingers s newSt
                                let newSt' = addFinger s newSt
                                return newSt'
                          otherwise -> return (addFinger bootstrap newSt) -- HER ER DET NOE RART!
-- }}}
                        
-- {{{ buildFingers
buildFingers c st = do
                      let f = (remoteFindSuccessor st c)
                          fsid i = (cNodeId (self st)) + (2 ^ (i - 1))
                          nodids = map fsid r
                          r = [1 .. (fromIntegral . m $ st)]
                      fingers <- sequence $ map f nodids
                      let newSt = st {fingerTable = Map.fromList . (remErr []) $ zip r fingers}
                      return newSt
    where remErr :: [(a,b)] -> [(a,Either c b)] -> [(a,b)]
          remErr ys ((k, Right c):xs) = remErr ((k,c):ys) xs -- ^ Fjerner successors som ikke ga noe treff
          remErr ys (x:xs) = remErr ys xs
          remErr ys [] = ys
-- }}}

-- {{{ closestPrecedingNode
closestPrecedingNode st id = helper st f id bits
    where f = fingerTable st
          bits = fromIntegral . m $ st

helper :: (Ord k, Num k) => NodeState -> Map.Map k Contact -> NodeId -> k -> Contact
helper st conts id 0 = error "error in closest node"
helper st conts id n
  | Map.null conts = (self st)
  | (Just c) <- lookopAndIf c conts n = c
  | otherwise = helper st conts id (n-1)
    where c1 x = (cNodeId $ self st) < (cNodeId x)
          c2 x = (cNodeId x) <= id
          c x = True
          --c x = (c1 x) && (c2 x)


-- | Lookup a value, if a predicate on it is true, return it, else Nothing
lookopAndIf :: (Ord k) => (a -> Bool) -> Map.Map k a -> k -> Maybe a
lookopAndIf f m k
  | (Just a) <- Map.lookup k m
  , f a = Just a
  | otherwise = Nothing
-- }}}

-- {{{ utility
codeMsg ::  (Bin.Binary a) => a -> [Char]
codeMsg = BS.Char8.unpack . Bin.encode

decodeMsg ::  (Bin.Binary a) => [Char] -> a
decodeMsg = Bin.decode . BS.Char8.pack
-- }}}
