{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Examples.TimingGames.TimingGameGraphsAnalysisWait where


import           Algebra.Graph.Relation
import qualified Data.Map.Strict      as M

import           Engine.Engine
import           Examples.TimingGames.GraphGames.InternalWait
import           Examples.TimingGames.GraphGames.TypesFunctions

-------------------------
-- Equilibrium definition

-- eq definition
eqTwoRoundGameWait p0 p1 p2 a10 a20 a11 a21 a12 a22 reward fee strategy context = generateOutput $ evaluate (twoRoundGameWait p0 p1 p2 a10 a20 a11 a21 a12 a22 reward fee) strategy context

eqOneRoundGameWait p0 p1 a10 a20 a11 a21 reward fee strategy context = generateOutput $ evaluate (repeatedGameWait p0 p1 a10 a20 a11 a21 reward fee) strategy context



-----------------------
-- Strategies

-- build on the head which has received the most votes?
-- that is a strategy as targeted by the protocol
strategyProposerWait :: Kleisli Stochastic (Timer, Chain) (Send Id)
strategyProposerWait = Kleisli (\(_,chain) -> pure $ Send $ determineHead chain)

-- deviating strategy for proposer -- do not send
strategyProposerWait1 :: Kleisli Stochastic (Timer, Chain) (Send Id)
strategyProposerWait1 = pureAction DoNotSend


-- vote for the head which has received the most votes?
-- that is a strategy as targeted by the protocol
strategyAttester :: Kleisli Stochastic (Timer, Chain, Chain) Id
strategyAttester = Kleisli (\(_,chainNew,_) -> pure $ determineHead chainNew)

-- Combining strategies for a single stage -- waiting
strategyOneRoundWait = strategyProposerWait ::- strategyAttester ::- strategyAttester ::- Nil
strategyOneRoundWait1 = strategyProposerWait1 ::- strategyAttester ::- strategyAttester  ::- Nil

-- Combining strategies for several stages
strategyTupleWait = strategyOneRoundWait +:+ strategyOneRoundWait
strategyTupleWait1 = strategyOneRoundWait1 +:+ strategyOneRoundWait



---------------------
-- Initial conditions

-- Initial linear chain with two votes per block
initialChainLinear = path [(1,2),(2,2),(3,2)]

-- Initial forked chain
initialChainForked = edges [((1,2),(2,2)),((1,2),(4,0)),((2,2),(3,4))]

-- Initial hashMap for last rounds players
-- assuming they both voted for the same block (3)
-- NOTE names have to match game definition
initialMap :: AttesterMap
initialMap = M.fromList [("a10",3),("a20",3)]



-- Initial context for linear chain, all initiated at the same ticker time, and an empty hashMap
initialContextLinear :: StochasticStatefulContext
                          (Timer, Timer, Chain, M.Map Player Id)
                          ()
                          (Timer, Stochastic Int, Chain, AttesterMap)
                          ()
initialContextLinear = StochasticStatefulContext (pure ((),(0,0,initialChainLinear,initialMap))) (\_ _ -> pure ())




initialContextLinear2 :: StochasticStatefulContext
                          (Timer, Timer, Timer, Timer, Chain, M.Map Player Id)
                          ()
                          ()
                          ()
initialContextLinear2 = StochasticStatefulContext (pure ((),(0,0,0,0,initialChainLinear,initialMap))) (\_ _ -> pure ())

initialContextForked :: StochasticStatefulContext
                          (Timer, Timer, Chain, M.Map Player Id)
                          ()
                          (Timer, Stochastic Timer, Chain, M.Map Player Id)
                          ()
initialContextForked = StochasticStatefulContext (pure ((),(0,0,initialChainForked,initialMap))) (\_ _ -> pure ())



-------------------
-- Scenarios Tested
{-
eqTwoRoundGame "p0" "p1" "p2" "a10" "a20" "a11" "a21" "a12" "a22" 2 2 strategyTuple initialContextLinear

eqOneRoundGame "p0" "p1" "a10" "a20" "a11" "a21" 2 2 strategyOneRound initialContextForked

eqTwoRoundGameWait "p0" "p1" "p2" "a10" "a20" "a11" "a21" "a12" "a22" 2 2 strategyTupleWait initialContextLinear
-}
