{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Examples.TimingGames.TimingGameGraphsAnalysis where


import           Algebra.Graph.Relation
import qualified Data.Map.Strict      as M

import           Engine.Engine
import           Examples.TimingGames.GraphGames.Internal

-- TODO Player 1 action deviation does not make sense in the alternative strategy. Is the evaluation of strategy wrong?
-- TODO add context for twoRoundGame? Currently, second proposer is not incentivized (payoffs happen only in period after)
-- TODO Markov game test is then for checking the various states of timer

------------------------
-- Analysis 2 round game

-- eq definition
eqTwoRoundGame p0 p1 p2 a10 a20 a11 a21 a12 a22 reward fee strategy context = generateOutput $ evaluate (twoRoundGame p0 p1 p2 a10 a20 a11 a21 a12 a22 reward fee) strategy context

eqRepeatedGame p0 p1 a10 a20 a11 a21 reward fee strategy context = generateIsEq $ evaluate (repeatedGame p0 p1 a10 a20 a11 a21 reward fee) strategy context

eqTest = eqRepeatedGame "p0" "p1" "a10" "a20" "a11" "a21"  2 2

initialMapTest ::  M.Map Player Id
initialMapTest = M.fromList [("a10",3),("a20",3)]


contextTest :: (Timer,Timer,Chain,M.Map Player Id, Id)
contextTest = (0,0,initialChainLinear,initialMapTest,3)

initialContextLinearTest :: StochasticStatefulContext
                       (Timer, Timer, Relation (Id, Vote), M.Map Player Id, Id)
                       ()
                       (Timer, Stochastic Int, Chain, M.Map Player Id, Id)
                       ()
initialContextLinearTest = StochasticStatefulContext (pure ((),contextTest)) (\_ _ -> pure ())
-----------------------
-- Strategies

-- build on the head which has received the most votes?
-- that is a strategy as targeted by the protocol
strategyProposer :: Kleisli Stochastic (Timer, Chain) Id
strategyProposer = Kleisli (\(_,chain) -> pure $ determineHead chain)

strategyProposer1 :: Kleisli Stochastic (Timer, Chain) Id
strategyProposer1 = pureAction 1


-- vote for the head which has received the most votes?
-- that is a strategy as targeted by the protocol
strategyAttester :: Kleisli Stochastic (Timer, Chain, Chain) Id
strategyAttester = Kleisli (\(_,chainNew,_) -> pure $ determineHead chainNew)

-- Combining strategies
strategyOneRound = strategyProposer ::- strategyAttester ::- strategyAttester ::- Nil

strategyTuple = strategyOneRound +:+ strategyOneRound

strategyTuple1 = strategyProposer1 ::- strategyAttester ::- strategyAttester ::- strategyProposer ::- strategyAttester ::- strategyAttester ::- Nil
---------------------
-- Initial conditions

-- Initial linear chain with two votes per block
initialChainLinear = path [(1,2),(2,2),(3,2)]

-- Initial hashMap for last rounds players
-- assuming they both voted for the same block (3)
-- NOTE names have to match game definition
initialMap = initialMapTest

-- Initial context for linear chain, all initiated at the same ticker time, and an empty hashMap
initialContextLinear :: StochasticStatefulContext
                          (Timer, Timer, Timer, Timer, Chain, M.Map Player Id, Id)
                          ()
                          ()
                          ()
initialContextLinear = StochasticStatefulContext (pure ((),(0,0,0,0,initialChainLinear,initialMap,3))) (\_ _ -> pure ())

-------------------
-- Scenarios Tested
{-
eqTwoRoundGame "p0" "p1" "p2" "a10" "a20" "a11" "a21" "a12" "a22" 2 2 strategyTuple initialContextLinear

eqTest strategyOneRound initialContextLinearTest
-}



{-

CURRENTLY NOT USED

-- NOTE Both players truthtelling is also an equilibrium
eq 2 strategyTuple (1,0,"a","")
eq 2 strategyTuple (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple (1,0,"a","a")
eq 2 strategyTuple (0,0,"a","a")


-- NOTE this is a scenario where both players coordinate against the true value; but the strategy of the attester is irrelevant here as he only sees the same information
eq 2 strategyTuple2 (1,0,"a","")
eq 2 strategyTuple2 (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple2 (1,0,"a","a")
eq 2 strategyTuple2 (0,0,"a","a")

-- NOTE proposer not telling the truth but attester is, is also an equilibrium. Makes sense as the attester can only attest what is there
eq 2 strategyTuple3 (1,0,"a","")
eq 2 strategyTuple3 (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple3 (1,0,"a","a")
eq 2 strategyTuple3 (0,0,"a","a")

-- NOTE proposer telling the truth but attester is not, is _not_ an equilibrium.
eq 2 strategyTuple4 (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple4 (0,0,"a","a")

-- NOTE the behavior above depends on the state!
eq 2 strategyTuple4 (1,0,"a","")
eq 2 strategyTuple4 (1,0,"a","a")



strategyProposer2 :: Kleisli Stochastic Int Send
strategyProposer2 = pureAction Send

strategyProposer' :: Kleisli Stochastic Int Send
strategyProposer' = pureAction DoNotSend

strategyAttester2 :: Kleisli Stochastic (Int, String, String) String
strategyAttester2 = Kleisli (\(_, newHash, _) -> pure newHash)

strategyAttester' :: Kleisli Stochastic (Int, String, String) String
strategyAttester' = Kleisli (\(_, _, oldHash) -> pure oldHash)

strategyAttester'' :: Kleisli Stochastic (Int, String, String) String
strategyAttester'' = Kleisli (\(_, newHash, oldHash) -> uniformDist [newHash,oldHash])



-}
