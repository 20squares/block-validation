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
eqTwoRoundGame p0 p1 p2 a10 a20 a11 a21 a12 a22 reward fee delayTreshold strategy context = generateIsEq $ evaluate (twoRoundGame p0 p1 p2 a10 a20 a11 a21 a12 a22 reward fee delayTreshold) strategy context


-----------------------
-- Strategies

-- build on the head which has received the most votes?
-- that is a strategy as targeted by the protocol
strategyProposer :: Kleisli Stochastic (Timer, Chain) (Send Id)
strategyProposer = Kleisli (\(_,chain) ->
                                  let headS = determineHead chain
                                      lsHead = S.elems headS
                                      in if length lsHead == 1
                                         then pure $ Send $ head lsHead
                                         else do
                                               drawHead <- uniformDist lsHead
                                               pure $ Send drawHead)

-- deviating strategy for proposer -- do not send
strategyProposer1 :: Kleisli Stochastic (Timer, Chain) (Send Id)
strategyProposer1 = pureAction DoNotSend


-- vote for the head which has received the most votes?
-- that is a strategy as targeted by the protocol
strategyAttester :: Kleisli Stochastic (Timer, Chain, Chain) Id
strategyAttester =
  Kleisli (\(_,chainNew,_) -> let headS = determineHead chainNew
                                  lsHead = S.elems headS
                                   in if length lsHead == 1
                                         then pure $ head lsHead
                                         else do
                                               drawHead <- uniformDist lsHead
                                               pure $ drawHead)

-- Combining strategies for a single stage -- waiting
strategyOneRound = strategyProposer ::- strategyAttester ::- strategyAttester ::- Nil
strategyOneRound1 = strategyProposer1 ::- strategyAttester ::- strategyAttester  ::- Nil

-- Combining strategies for several stages
strategyTuple = strategyOneRound +:+ strategyOneRound
strategyTuple1 = strategyOneRound1 +:+ strategyOneRound



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
