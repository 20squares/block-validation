{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Examples.TimingGames.ExogenousTicker where


import           Algebra.Graph.Relation
import qualified Data.Map.Strict      as M
import qualified Data.Set             as S

import           Engine.Engine
import           Examples.TimingGames.GraphGames.InternalOverlappingTicker
import           Examples.TimingGames.GraphGames.TypesFunctions
-------------------------
-- Equilibrium definition

eqTwoRoundGameWait p0 p1 p2 a10 a20 a11 a21 a12 a22 reward fee ticker1 delayedTicker1 ticker2 delayedTicker2 threshold1 threshold2 strategy context = generateOutput $ evaluate (twoRoundGameWaitExogTicker p0 p1 p2 a10 a20 a11 a21 a12 a22 reward fee ticker1 delayedTicker1 ticker2 delayedTicker2 threshold1 threshold2) strategy context


-----------------------
-- Strategies

-- build on the head which has received the most votes?
-- that is a strategy as targeted by the protocol
strategyProposerWait :: Kleisli Stochastic (Timer, Chain) (Send Id)
strategyProposerWait = Kleisli (\(_,chain) ->
                                  let headS = determineHead chain
                                      lsHead = S.elems headS
                                      in if length lsHead == 1
                                         then pure $ Send $ head lsHead
                                         else do
                                               drawHead <- uniformDist lsHead
                                               pure $ Send drawHead)

-- deviating strategy for proposer -- do not send
strategyProposerWait1 :: Kleisli Stochastic (Timer, Chain) (Send Id)
strategyProposerWait1 = pureAction DoNotSend

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
                          (Chain, AttesterMap, Id)
                          ()
                          (Chain, AttesterMap, Id)
                          ()
initialContextLinear = StochasticStatefulContext (pure ((),(initialChainLinear, initialMap, 3))) (\_ _ -> pure ())




initialContextForked :: StochasticStatefulContext
                          (Chain, AttesterMap, Id )
                          ()
                          (Chain, AttesterMap, Id)
                          ()
initialContextForked = StochasticStatefulContext (pure ((),(initialChainForked, initialMap, 3))) (\_ _ -> pure ())



-------------------
-- Scenarios Tested
{-
eqTwoRoundGameWait "p0" "p1" "p2" "a10" "a20" "a11" "a21" "a12" "a22" 2 2 0 0 0 0 0 12  strategyTupleWait initialContextLinear
-}
