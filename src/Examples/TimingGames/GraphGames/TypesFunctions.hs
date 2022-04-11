{-# LANGUAGE DatatypeContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Examples.TimingGames.GraphGames.TypesFunctions where

import           Engine.Engine

import           Algebra.Graph.Relation
import qualified Data.Map.Strict      as M
import qualified Data.Set             as S

----------
-- 0 Types
----------
-- HashBlock choice
data (Eq a, Ord a, Show a) => Send a = Send a | DoNotSend
   deriving (Eq,Ord,Show)

-- A view on the previous information
data View a = HashBlock a | Empty
   deriving (Eq,Ord,Show)

type Started = Bool

type Hash = Word
type Player = String
type Vote = Int
type Id    = Int
type Timer = Int
type Weight = Int
type AttesterMap = M.Map Player Id
-- The chain is represented by the edges (Blocks) and vertices (Which attester voted for that Block to be the head)
type Chain = Relation (Id,Vote)
type WeightedChain = Relation (Id,Weight)

------------------------
-- 1 Auxiliary functions
------------------------

-- Given a previous chain, id, and a new hash, extend the chain accordingly
-- initially, that vertex has empty votes
-- it is assigned a unique id
-- FIXME What if non existing id?
addToChain :: Chain -> Id -> Chain
addToChain chain id  =
  let newId = vertexCount chain + 1
      -- ^ assign new id using the vertexCount of the existing chain
      newNode = vertex (newId,0)
      -- ^ create new vertex with 0 votes
      vertexRoot = induce (\(x,_) -> x == id) chain
      -- ^ find vertex with the _id_
      newConnection = connect vertexRoot newNode
      -- ^ connect the vertex with the relevant id to new node with label new hash
      in overlay chain newConnection
      -- ^ update the connection of the new chain

-- Given a previous chain and the decision to append or to wait,
-- produce a new chain
addToChainWait :: Chain -> Send Id -> Chain
addToChainWait chain DoNotSend  = chain
-- ^ Keep the old chain
addToChainWait chain (Send id)  = addToChain chain id
-- ^ Append block to old chain (create new chain)


-- Given a previous chain and the decision to append or to wait, a timer and a timer threshold
-- produce a new chain
addToChainWaitTimer :: Timer -> Timer -> Chain ->  Send Id -> Chain
addToChainWaitTimer threshold timer chain decision =
  if timer == threshold
     then addToChainWait chain decision
          -- ^ only at the time of the threshold a new block is added
     else chain
          -- ^ otherwise the same block is kept

-- Produces alternatives for proposer
alternativesProposer :: (Timer, Chain) -> [Send Id]
alternativesProposer (_,chain) =
  let noVertices = vertexCount chain
      in DoNotSend : fmap Send [1..noVertices]

-- Find vertex in a chain given unique id
-- FIXME What if non-existing id?
findVertexById :: Chain -> Id -> (Id,Vote)
findVertexById chain id =
  let  verticeLs = vertexList chain
       -- ^ list of vertices
       in (head $ filter (\(id',_) -> id' == id) verticeLs)

-- For attester choose the string which he believes is the head and update the chain accordingly
-- FIXME What if non-existing id?
attesterChoiceIndex :: Chain -> Id -> Chain
attesterChoiceIndex chain id =
  let (id',i) = findVertexById chain id
      in replaceVertex (id',i) (id',i+1) chain

-- Given an initial chain and a list of votes on _Id_s, update the chain
-- FIXME What if non-existing id?
updateVotes :: Chain -> [Id] -> Chain
updateVotes chain [] = chain
updateVotes chain (i:is) = updateVotes (attesterChoiceIndex chain i) is

-- Cycling ticker
transformTicker :: Timer -> Timer
transformTicker 12 = 0
transformTicker x  = x + 1


-- find the head of the chain
determineHead :: Chain -> Id
determineHead chain =
  let allBranches = findBranches chain
      weightedBranches = S.map (findPath chain) allBranches
      (weightMax,idMax) = S.findMax $ S.map (\(x,y) -> (y,x)) weightedBranches
      in idMax
  where
    -- find all the branches of a chain
    findBranches :: Chain  -> S.Set (Id,Vote)
    findBranches chain' =
      let  vertexSetChain   = vertexSet chain'
           transChain = transitiveClosure chain'
           setPreSet = S.unions $ S.map (flip preSet transChain) vertexSetChain
           in S.difference vertexSetChain setPreSet
    -- find all the paths from each branch to the root of the chain
    findPath :: Chain -> (Id, Vote) -> (Id, Weight)
    findPath chain' (i,v) =
      let elementsOnPath = preSet (i,v) transitiveChain
          transitiveChain = transitiveClosure chain'
          weight = S.foldr (\(_,j) -> (+) j) 0 elementsOnPath
          in (i,weight + v)
          -- ^ NOTE the value of the last node itself is added as well

-- Is the node the attester voted for on the path to the latest head?
-- FIXME player name, id not given
attestedCorrect :: Player -> M.Map Player Id -> Chain -> Id -> Bool
attestedCorrect name map chain headOfChain =
  let idChosen = map M.! name
      -- ^ id voted for by player
      chosenNode = findVertexById chain idChosen
      -- ^ vertex chosen
      headNode = findVertexById chain headOfChain
      -- ^ vertex which is head of the chain
      chainClosure = closure chain
      -- ^ transitive closure of chain; needed to get all connections
      setOnPath = postSet chosenNode chainClosure
      -- ^ elements that are successors of id'
      in S.member headNode setOnPath
      -- ^ is the head in that successor set?

-- Is there a difference between the head from period t-2 and the head of period t-1?
-- Is used to determine whether the proposer in t-1 actually did something
wasBlockSent :: Chain -> Id -> (Bool,Id)
wasBlockSent chainT1 idT2 =
  let headT1 = determineHead chainT1
      wasSent = idT2 + 1 == headT1
      in (wasSent,headT1)

-- Did the proposer from (t-1) send the block? Gets rewarded if that block is on the path to the current head.
proposedCorrect :: Bool -> Chain -> Bool
proposedCorrect False _     = False
proposedCorrect True chain  =
  let currentHeadId = determineHead chain
      currentHead   = findVertexById chain currentHeadId
      oldDecisionProposer = vertexCount chain - 1
      chainClosure  = closure chain
      onPathElems   = preSet currentHead chainClosure
      pastHead      = findVertexById chain oldDecisionProposer
      in S.member pastHead onPathElems


-- draw from a timer which determines whether the message is delayed
delaySendTime :: Int -> Int ->  Stochastic Int
delaySendTime actualTimer delayedTimer
  | actualTimer ==  0       = distFromList [(0,0.5),(5,0.5)]
  | delayedTimer == 5 = playDeterministically delayedTimer
  | otherwise         = playDeterministically actualTimer

-- given timers send old message or new message
delayMessage :: (Timer, Timer, Chain, Chain) -> Chain
delayMessage (actualTimer, delayedTimer, oldChain, newChain)
  | actualTimer < delayedTimer = oldChain
  | otherwise                  = newChain




-- transform list to Map; done here due to restrictions of DSL
newAttesterMap :: [(Player,Id)] -> AttesterMap -> AttesterMap
newAttesterMap new old = M.union (M.fromList new) old

------------
-- 2 Payoffs
------------

  -- The attester  and the proposer are rewarded if their decision has been evaluated by _attestedCorrect_ resp. _proposedCorrect_ as correct
attesterPayoff successFee verified = if verified then successFee else 0
proposerPayoff reward verified  = if verified then reward else 0

