{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}

module Examples.BlockValidation.Attack where


import           Algebra.Graph.Relation
import           Control.Monad.State                hiding (state)
import qualified Data.Map.Strict      as M
import qualified Data.Set             as S

import           Data.Utils
import           Engine.Engine
import           Examples.BlockValidation.Representations.Internal
import           Examples.BlockValidation.Representations.TypesFunctions

---------------------------------------------------------------
-- Here we test the assumption that a misrepresenting proposer,
-- by waiting sufficiently long, can cause a problem for the
-- protocol
---------------------------------------------------------------


-------------------------
-- Equilibrium definition

eqOneEpisodeGame p0 p1 a10 a20 a11 a21 reward fee delayTreshold strategy context = generateIsEq $ evaluate (oneEpisodeAttack p0 p1 a10 a20 a11 a21 reward fee delayTreshold) strategy context


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


-- vote for the head which has received the most votes
-- in case of a tie, choose the block from the current proposer
strategyValidator4 :: Kleisli Stochastic (Timer, Chain, Chain) Id
strategyValidator4 =
  Kleisli (\(_,chainNew,_) -> let headS = determineHead chainNew
                                  lsHead = S.elems headS
                                   in if length lsHead == 1
                                         then pure $ head lsHead
                                         else do
                                               pure 4)

-- vote for the head which has received the most votes
-- in case of a tie, choose the block from the current proposer
strategyValidator5 :: Kleisli Stochastic (Timer, Chain, Chain) Id
strategyValidator5 =
  Kleisli (\(_,chainNew,_) -> let headS = determineHead chainNew
                                  lsHead = S.elems headS
                                   in if length lsHead == 1
                                         then pure $ head lsHead
                                         else do
                                               pure 5)


-- Combining strategies for a single stage -- validator voting for 4
strategyOneRound4 = strategyProposer ::- strategyValidator4 ::- strategyValidator4 ::- Nil

-- Combining strategies for a single stage -- validator voting for 4
strategyOneRound5 = strategyProposer ::- strategyValidator5 ::- strategyValidator5 ::- Nil

---------------------
-- Initial conditions

-- Initial linear chain with two votes per block
initialChainLinear = path [(1,2),(2,2),(3,2)]

-- Mainpulated chain which comes in second by the proposer from round before
manipulatedChain   = path [(1,2),(2,2),(3,2),(5,0)]

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
                          (Timer, Chain, Id, AttesterMap, Chain)
                          ()
                          (Chain, Id, AttesterMap)
                          ()
initialContextLinear p a1 a2 reward successFee = StochasticStatefulContext (pure ((),(0, initialChainLinear, 3, initialMap, manipulatedChain))) (\_ x -> feedPayoffs p a1 a2 reward successFee x)

-- We need to embed the future reward for the players of that single round
feedPayoffs :: Player -> Player -> Player -> Reward -> Fee -> (Chain, Id, AttesterMap) -> StateT Vector Stochastic ()
feedPayoffs p a1 a2 reward successFee (newChain,headOfChainIdT1,attesterHashMapNew) = do
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


-------------------
-- Scenarios Tested
{-
eqOneEpisodeGame "p0" "p1" "a10" "a20" "a11" "a21" 2 2 0 strategyOneEpisode4 (initialContextLinear "p1" "a11" "a21" 2 2)

eqOneEpisodeGame "p0" "p1" "a10" "a20" "a11" "a21" 2 2 0 strategyOneEpisode5 (initialContextLinear "p1" "a11" "a21" 2 2)
-}