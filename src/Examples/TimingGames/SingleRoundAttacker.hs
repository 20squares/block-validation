{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}

module Examples.TimingGames.SingleRoundAttacker where


import           Algebra.Graph.Relation
import           Control.Monad.State                hiding (state)
import qualified Data.Map.Strict      as M
import qualified Data.Set             as S

import           Data.Utils
import           Engine.Engine
import           Examples.TimingGames.GraphGames.Internal
import           Examples.TimingGames.GraphGames.TypesFunctions

---------------------------------------------------------------
-- Here we test the assumption that a misrepresenting proposer,
-- by waiting sufficiently long, can cause a problem for the
-- protocol
---------------------------------------------------------------


-------------------------
-- Equilibrium definition

eqOneRoundGame p0 p1 a10 a20 a11 a21 reward fee delayTreshold strategy context = generateOutput $ evaluate (oneEpisode p0 p1 a10 a20 a11 a21 reward fee delayTreshold) strategy context


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
strategyProposer1 = pureAction $ Send 3

-- vote for the head which has received the most votes
-- in case of a tie, choose the block from last round
strategyValidator :: Kleisli Stochastic (Timer, Chain, Chain) Id
strategyValidator =
  Kleisli (\(_,chainNew,_) -> let headS = determineHead chainNew
                                  lsHead = S.elems headS
                                   in if length lsHead == 1
                                         then pure $ head lsHead
                                         else do
                                               pure $ 4)

-- vote for the head which has received the most votes?
-- in case of a tie, randomize
strategyValidator1 :: Kleisli Stochastic (Timer, Chain, Chain) Id
strategyValidator1 =
  Kleisli (\(_,chainNew,_) -> let headS = determineHead chainNew
                                  lsHead = S.elems headS
                                   in if length lsHead == 1
                                         then pure $ head lsHead
                                         else do
                                               drawHead <- uniformDist lsHead
                                               pure $ drawHead)

-- Combining strategies for a single stage -- waiting
strategyOneRound = strategyProposer ::- strategyValidator ::- strategyValidator ::- Nil
strategyOneRound1 = strategyProposer1 ::- strategyValidator ::- strategyValidator  ::- Nil
strategyOneRound2 = strategyProposer1 ::- strategyValidator1 ::- strategyValidator1  ::- Nil

---------------------
-- Initial conditions

-- Initial linear chain with two votes per block
-- NOTE we assume that there is an un-voted block
-- That was created by the deviating proposer _(4,0)_
-- The idea is that it was created after the attesters
-- from that block could actually vote
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
                          (Timer, Chain, Id, AttesterMap)
                          ()
                          (Chain, Id, AttesterMap)
                          ()
initialContextLinear p a1 a2 reward successFee = StochasticStatefulContext (pure ((),(0, initialChainLinear, 3, initialMap))) (\_ x -> feedPayoffs p a1 a2 reward successFee x)

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
eqOneRoundGame "p0" "p1" "a10" "a20" "a11" "a21" 2 2 0 strategyOneRound (initialContextLinear "p1" "a11" "a21" 2 2)
-}
