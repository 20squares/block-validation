{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Examples.TimingGames.Analysis where


import           Algebra.Graph.Relation
import qualified Data.Map.Strict      as M
import qualified Data.Set             as S

import           Engine.Engine
import           Examples.TimingGames.GraphGames.Internal
import           Examples.TimingGames.GraphGames.TypesFunctions

-------------------------
-- Equilibrium definition

-- eq definition
eqTwoEpisodeGame p0 p1 p2 a10 a20 a11 a21 a12 a22 reward fee delayTreshold strategy context = generateIsEq $ evaluate (twoEpisodeGame p0 p1 p2 a10 a20 a11 a21 a12 a22 reward fee delayTreshold) strategy context


-----------------------
-- Strategies

-- Attach a new block on the head which has received the most votes.
-- If there are multiple heads with the same number of votes, randomize uniformly.
-- NOTE: This models a strategy of an honest proposer targeted by the protocol
strategyProposer :: Kleisli Stochastic (Timer, Chain) (Send Id)
strategyProposer = Kleisli (\(_,chain) ->
                                  let headS = determineHead chain
                                      lsHead = S.elems headS
                                      in if length lsHead == 1
                                         then pure $ Send $ head lsHead
                                         else do
                                               drawHead <- uniformDist lsHead
                                               pure $ Send drawHead)
                                         -- ^ Under normal working conditions of the protocol, that conditional will never kick in

-- Vote for the head which has received the most votes.
-- If there are multiple heads with the same number of votes, randomize uniformly which head to vote on.
-- NOTE: This models a strategy of an honest validator targeted by the protocol
strategyValidator :: Kleisli Stochastic (Timer, Chain, Chain) Id
strategyValidator =
  Kleisli (\(_,chainNew,_) -> let headS = determineHead chainNew
                                  lsHead = S.elems headS
                                   in if length lsHead == 1
                                         then pure $ head lsHead
                                         else do
                                               drawHead <- uniformDist lsHead
                                               pure $ drawHead)
                                         -- ^ Under normal working conditions of the protocol, that conditional will never kick in

-- Combining strategies for a single stage -- waiting
strategyOneRound = strategyProposer ::- strategyValidator ::- strategyValidator ::- Nil

-- Combining strategies for two stages
strategyTuple = strategyOneRound +:+ strategyOneRound


---------------------
-- Initial conditions

-- Initial linear chain with two votes per block
initialChainLinear = path [(1,2),(2,2),(3,2)]

-- Initial hashMap for last rounds players
-- assuming they both voted for the same block (3)
-- NOTE names have to match game definition
initialMap :: AttesterMap
initialMap = M.fromList [("a10",3),("a20",3)]


-- Initial context for linear chain, all initiated at the same ticker time, and an empty hashMap
initialContextLinear :: StochasticStatefulContext
                          (Timer, Chain, Id, M.Map Player Id)
                          ()
                          (Timer, Chain, Id, AttesterMap)
                          ()
initialContextLinear = StochasticStatefulContext (pure ((),(0,initialChainLinear, 3, initialMap))) (\_ _ -> pure ())

-------------------
-- Scenarios Tested
{-
eqTwoRoundGame "p0" "p1" "p2" "a10" "a20" "a11" "a21" "a12" "a22" 2 2 0 strategyTuple initialContextLinear
-}
