{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}

module Examples.TimingGames.WaitingProposer where


import           Algebra.Graph.Relation
import           Control.Monad.State                hiding (state)
import qualified Data.Map.Strict      as M
import qualified Data.Set             as S

import           Data.Utils
import           Engine.Engine
import           Examples.TimingGames.GraphGames.InternalWait
import           Examples.TimingGames.GraphGames.TypesFunctions

---------------------------------------------------------------
-- Here we test the assumption that a misrepresenting proposer,
-- by waiting sufficiently long, can cause a problem for the
-- protocol
---------------------------------------------------------------


-------------------------
-- Equilibrium definition

eqOneRoundGameWait p0 p1 a10 a20 a11 a21 reward fee strategy context = generateOutput $ evaluate (oneRoundWait p0 p1 a10 a20 a11 a21 reward fee) strategy context


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
strategyProposerWait1 = pureAction $ Send 3

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


---------------------
-- Initial conditions

-- Initial linear chain with two votes per block
-- NOTE we assume that there is an un-voted block
-- That was created by the deviating proposer _(4,0)_
initialChainLinear = path [(1,2),(2,2),(3,2),(4,0)]


-- Initial hashMap for last rounds players
-- assuming they both voted for the same block (3)
-- NOTE names have to match game definition
initialMap :: AttesterMap
initialMap = M.fromList [("a10",3),("a20",3)]



-- Initial context for linear chain, all initiated at the same ticker time, and an empty hashMap
initialContextLinear :: Player
                     -> Player
                     -> Player
                     -> Reward
                     -> Fee
                     -> StochasticStatefulContext
                          (Timer, Timer, Chain, Id, AttesterMap)
                          ()
                          (Stochastic Timer, Chain, Id, AttesterMap)
                          ()
initialContextLinear p a1 a2 reward successFee = StochasticStatefulContext (pure ((),(0,0,initialChainLinear, 3, initialMap))) (\_ x -> feedPayoffs p a1 a2 reward successFee x)

-- We need to embed the future reward for the players of that single round
feedPayoffs :: Player -> Player -> Player -> Reward -> Fee -> (Stochastic Timer, Chain, Id, AttesterMap) -> StateT Vector Stochastic ()
feedPayoffs p a1 a2 reward successFee (_,newChain,headOfChainIdT1,attesterHashMapNew) = do
  let headOfChainNew    = determineHead newChain
      attestedCorrectA1 = attestedCorrect a1 attesterHashMapNew newChain headOfChainNew
      attestedCorrectA2 = attestedCorrect a2 attesterHashMapNew newChain headOfChainNew
      payoffA1          = attesterPayoff successFee attestedCorrectA1
      payoffA2          = attesterPayoff successFee attestedCorrectA2
      (blockWasSent,_)  = wasBlockSent newChain headOfChainIdT1
      proposerCorrect   = proposedCorrect blockWasSent newChain
      payoffProposer    = proposerPayoff reward proposerCorrect
  modify (adjustOrAdd (\x -> x + payoffA1) payoffA1 a1)
  modify (adjustOrAdd (\x -> x + payoffA2) payoffA2 a2)
  modify (adjustOrAdd (\x -> x + payoffProposer) payoffProposer p) 
  -- compute payoff for attester in the one round game

------------------------------------------------------------------
-- TODO delete all below when ready
  -- compute payoff for proposer in the one round game
testChain :: Chain
testChain = edges [((1,2),(2,2)),((2,2),(3,2)),((3,2),(4,0)),((3,2),(5,2))]

testMap :: AttesterMap
testMap = M.fromList [("a10",3),("a20",3),("a11",5),("a21",5)]

--testFunction :: Player -> Player -> Player -> Reward -> Fee -> (Stochastic Timer, Chain, Id, AttesterMap) -> Bool
testFunction p a1 a2 reward successFee (_,newChain,headOfChainIdT1,attesterHashMapNew) =
  let headOfChainNew    = determineHead newChain
      attestedCorrectA1 = attestedCorrect a1 attesterHashMapNew newChain headOfChainNew
      attestedCorrectA2 = attestedCorrect a2 attesterHashMapNew newChain headOfChainNew
      payoffA1          = attesterPayoff successFee attestedCorrectA1
      payoffA2          = attesterPayoff successFee attestedCorrectA2
      (blockWasSent,_)  = wasBlockSent newChain headOfChainIdT1
      proposerCorrect   = proposedCorrect blockWasSent newChain
      payoffProposer    = proposerPayoff reward proposerCorrect
      in proposerCorrect 
------------------------------------------------------------------
-------------------
-- Scenarios Tested
{-
eqOneRoundGameWait "p0" "p1" "a10" "a20" "a11" "a21" 2 2 strategyOneRoundWait (initialContextLinear "p1" "a11" "a21" 2 2)
-}
