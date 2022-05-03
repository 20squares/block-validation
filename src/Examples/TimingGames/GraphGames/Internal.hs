{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Examples.TimingGames.GraphGames.Internal where


import           Engine.Engine
import           Preprocessor.Preprocessor
import           Examples.TimingGames.GraphGames.TypesFunctions hiding (proposedCorrect, determineHead)
import           Examples.TimingGames.GraphGames.SharedBuildingBlocks hiding (proposerPayment)

import           Algebra.Graph.Relation
import           Control.Monad.State  hiding (state,void)
import qualified Control.Monad.State  as ST
import qualified Data.Map.Strict      as M
import qualified Data.Set             as S

--------------------------------------------
-- Multiplayer version of the protocol
-- State for each game is a model of a chain

-- TODO Put proposers' decisions also in a map; to have access to earlier player ids
-- TODO For how long will the renumeration of attesters and proposer continue? Is it just for one period? Periods t?


----------
-- A Model
----------

---------------------
-- 1 Game blocks

-- Given old has and chosen id, add a block
addBlock = [opengame|

    inputs    : chainOld, chosenId ;
    feedback  :   ;

    :-----:
    inputs    : chainOld, chosenId ;
    feedback  :   ;
    operation : forwardFunction $ uncurry addToChain ;
    outputs   : chainNew ;
    returns   : ;

    :-----:

    outputs   : chainNew ;
    returns   :          ;
  |]

 
-- A proposer observes the ticker and decides to append the block to a node
proposer  name = [opengame|

    inputs    : ticker, delayedTicker, chainOld;
    feedback  :   ;

    :-----:
    inputs    : ticker, chainOld ;
    feedback  :   ;
    operation : dependentDecision name (\(t,chainOld) -> [1,vertexCount chainOld]) ;
    outputs   : decisionProposer ;
    returns   : 0;
    // ^ decision which hash to send forward (latest element, or second latest element etc.)
    // ^ NOTE fix reward to zero; it is later updated where it is evaluated as correct or false

    inputs    : chainOld, decisionProposer ;
    feedback  :   ;
    operation : addBlock ;
    outputs   : chainNew;
    returns   : ;
    // ^ creates new hash at t=0


    inputs    : ticker, delayedTicker ;
    feedback  :   ;
    operation : forwardFunction $ uncurry delaySendTime ;
    outputs   : delayedTickerUpdate ;
    returns   : ;
    // ^ determines whether message is delayed or not

    inputs    : ticker, delayedTicker, chainOld, chainNew ;
    feedback  :   ;
    operation : forwardFunction $ delayMessage ;
    outputs   : messageChain ;
    returns   : ;
    // ^ for a given timer, determines whether the block is decisionProposer or not

    :-----:

    outputs   : messageChain, delayedTickerUpdate ;
    // ^ newchain (if timer allows otherwise old chain), update on delayedticker, decisionProposer
    returns   :  ;
  |]


-------------------
-- 2 Complete games
-------------------


--------------------- added for old version overwriting building blocks ------------------------
-- TODO change repeated version to actual setting once settled
-- Did the proposer from (t-1) send the block? Gets rewarded if that block is on the path to the current head.

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



proposedCorrect :: Chain -> Bool
proposedCorrect  chain  =
  let currentHeadId = determineHead chain
      currentHead   = findVertexById chain currentHeadId
      oldDecisionProposer = vertexCount chain - 1
      chainClosure  = closure chain
      onPathElems   = preSet currentHead chainClosure
      pastHead      = findVertexById chain oldDecisionProposer
      in S.member pastHead onPathElems



proposerPayment name reward = [opengame|

    inputs    : chainNew ;
    feedback  :   ;

    :-----:
    inputs    :  chainNew ;
    feedback  :   ;
    operation : forwardFunction $ proposedCorrect  ;
    outputs   : correctSent ;
    returns   : ;
    // ^ This determines whether the proposer was correct in period (t-1)


    inputs    : correctSent ;
    feedback  :   ;
    operation : updatePayoffProposer name reward;
    outputs   : ;
    returns   : ;
    // ^ Updates the payoff of the proposer given decision in period (t-1)

    :-----:

    outputs   : ;
    returns   :  ;
  |]

--------------------- added for old version overwriting building blocks ------------------------

  
-- One round game
oneRound p0 p1 a10 a20 a11 a21 reward fee = [opengame|

    inputs    : ticker, delayedTicker, chainOld, attesterHashMapOld  ;
    // ^ chainOld is the old hash
    feedback  :   ;

    :-----:
    inputs    : ticker,delayedTicker,chainOld ;
    feedback  :   ;
    operation : proposer p1;
    outputs   : chainNew, delayedTickerUpdate ;
    returns   : ;
    // ^ Proposer makes a decision, a new hash is proposed

    inputs    : ticker,chainNew,chainOld, attesterHashMapOld;
    feedback  :   ;
    operation : attestersGroupDecision a11 a21 ;
    outputs   : attesterHashMapNew, chainNewUpdated ;
    returns   :  ;
    // ^ Attesters make a decision

    inputs    : chainNewUpdated ;
    feedback  :   ;
    operation : determineHeadOfChain ;
    outputs   : headOfChainId ;
    returns   : ;
    // ^ Determines the head of the chain

    inputs    : attesterHashMapOld, chainNewUpdated, headOfChainId ;
    feedback  :   ;
    operation : attestersPayment a10 a20 fee ;
    outputs   : ;
    returns   : ;
    // ^ Determines whether attesters from period (t-1) were correct and get rewarded

    inputs    : chainNewUpdated ;
    feedback  :   ;
    operation : proposerPayment p0 reward ;
    outputs   :  ;
    returns   : ;
    // ^ This determines whether the proposer from period (t-1) was correct and triggers payments accordingly

    :-----:

    outputs   : attesterHashMapNew, chainNewUpdated, delayedTickerUpdate ;
    returns   :  ;
  |]



-- Repeated game
repeatedGame  p0 p1 a10 a20 a11 a21 reward fee = [opengame|

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRound p0 p1 a10 a20 a11 a21 reward fee ;
    outputs   : attesterHashMapNew, chainNew, delayedTickerUpdate ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    :-----:

    outputs   : tickerNew, delayedTickerUpdate, chainNew, attesterHashMapNew ;
    returns   :  ;
  |]



-- Two round game
-- Follows spec for two players
twoRoundGame  p0 p1 p2 a10 a20 a11 a21 a12 a22  reward fee = [opengame|

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRound p0 p1 a10 a20 a11 a21 reward fee ;
    outputs   : attesterHashMapNew, chainNew, delayedTickerUpdate ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    inputs    : ticker,delayedTicker, chainNew, attesterHashMapNew ;
    // NOTE ticker time is ignored here
    feedback  :   ;
    operation : oneRound p1 p2 a11 a21 a12 a22 reward fee ;
    outputs   : attesterHashMapNew2, chainNew2, delayedTickerUpdate2 ;
    returns   :  ;

    inputs    : tickerNew;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew2;
    returns   : ;



    :-----:

    outputs   : tickerNew2, delayedTickerUpdate2, chainNew2, attesterHashMapNew2 ;
    returns   :  ;
  |]






 





  
  
----------------
-- Continuations
-- extract continuation
-- extract continuation
extractContinuation :: StochasticStatefulOptic
                         (Timer, Timer, Chain, M.Map Player Id)
                         ()
                         (Timer, Stochastic Timer, Chain, M.Map Player Id)
                         ()
                    -> (Timer, Stochastic Timer, Chain, M.Map Player Id)
                    -> StateT Vector Stochastic ()
extractContinuation (StochasticStatefulOptic v u) (i, j, chain, map) = do
  j' <- ST.lift j
  let x = (i, j', chain, map)
  (z,a) <- ST.lift (v x)
  u z ()

-- extract next state (action)
extractNextState :: StochasticStatefulOptic
                       (Timer, Timer, Chain, M.Map Player Id)
                       ()
                       (Timer, Stochastic Timer, Chain , M.Map Player Id)
                       ()
                 -> (Timer, Stochastic Timer, Chain, M.Map Player Id)
                 -> Stochastic (Timer, Stochastic Timer, Chain, M.Map Player Id)
extractNextState (StochasticStatefulOptic v _) (i, j, chain, map) = do
  j' <- j
  let x = (i, j', chain, map)
  (z,a) <- v x
  pure a

-- determine continuation for iterator, with the same repeated strategy
determineContinuationPayoffs 1        strat action = pure ()
determineContinuationPayoffs iterator strat action = do
   extractContinuation executeStrat action
   nextInput <- ST.lift $ extractNextState executeStrat action
   determineContinuationPayoffs (pred iterator) strat nextInput
 where executeStrat =  play (repeatedGame "proposer" "proposerPast" "attester1" "attester2" "attester1past" "attester2Past" 2 2) strat


executeStrat strat =  play (repeatedGame "proposer" "proposerPast" "attester1" "attester2" "attester1past" "attester2Past" 2 2) strat

-- fix context used for the evaluation
contextCont iterator strat initialAction = StochasticStatefulContext (pure ((),initialAction)) (\_ action -> determineContinuationPayoffs iterator strat action)
