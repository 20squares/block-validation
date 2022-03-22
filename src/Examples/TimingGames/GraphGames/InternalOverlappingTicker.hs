{-# LANGUAGE DatatypeContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Examples.TimingGames.GraphGames.InternalOverlappingTicker where


import           Engine.Engine
import           Preprocessor.Preprocessor
import           Examples.TimingGames.GraphGames.TypesFunctions

import           Algebra.Graph.Relation
import           Control.Monad.State  hiding (state,void)
import qualified Control.Monad.State  as ST
import qualified Data.Map.Strict      as M
import           Data.NumInstances.Tuple
-- NOTE ^^ this is for satisfying the class restrictions of Algebra.Graph.Relation
import qualified Data.Set             as S
import           Data.Tuple.Extra (uncurry3)

------------
-- 2 Payoffs
------------

-- A proposer observes the ticker and decides to append the block to a node OR not
-- In other words, the proposer can wait to append the block
proposerWait  name = [opengame|

    inputs    : ticker, delayedTicker, chainOld;
    feedback  :   ;

    :-----:
    inputs    : ticker, chainOld ;
    feedback  :   ;
    operation : dependentDecision name  alternativesProposer;
    outputs   : decisionProposer ;
    returns   : 0;
    // ^ decision which hash to send forward (latest element, or second latest element etc.)
    // ^ NOTE fix reward to zero; it is later updated where it is evaluated as correct or false

    inputs    : chainOld, decisionProposer ;
    feedback  :   ;
    operation : addBlockWait ;
    outputs   : chainNew;
    returns   : ;
    // ^ creates new hash at t=0


    inputs    : ticker, delayedTicker, chainOld, chainNew ;
    feedback  :   ;
    operation : forwardFunction $ delayMessage ;
    outputs   : messageChain ;
    returns   : ;
    // ^ for a given timer, determines whether the block is decisionProposer or not

    :-----:

    outputs   : messageChain, delayedTicker ;
    // ^ newchain (if timer allows otherwise old chain), update on delayedticker, decisionProposer
    returns   :  ;
  |]



  
-- The attester observes the sent hash, the old hash, the timer, and can then decide which node to attest as the head
attester name = [opengame|

    inputs    : ticker,chainNew,chainOld ;
    feedback  :  ;

    :-----:
    inputs    : ticker,chainNew,chainOld ;
    feedback  :   ;
    operation : dependentDecision name (\(ticker, chainNew, chainOld) -> [1, vertexCount chainNew]) ;
    outputs   : attestedIndex ;
    returns   : 0 ;
    // ^ the attester either can send the newHash or the oldHash
    // ^ NOTE the payoff for the attester comes from the next period

    :-----:

    outputs   : attestedIndex ;
    returns   :  ;
  |]

updatePayoffAttester name fee  = [opengame|
    inputs    : bool ;
    feedback  :   ;

    :-----:
    inputs    : bool ;
    feedback  :   ;
    operation : forwardFunction $ attesterPayoff fee ;
    outputs   : value ;
    returns   : ;
    // ^ Determines the value


    inputs    : value ;
    feedback  :   ;
    operation : addPayoffs name ;
    outputs   : ;
    returns   : ;
    // ^ Could make sense to make sense to model this in period
    :-----:

    outputs   :  ;
    returns   :  ;

  |]

updatePayoffProposer name reward  = [opengame|
    inputs    : bool ;
    feedback  :   ;

    :-----:
    inputs    : bool ;
    feedback  :   ;
    operation : forwardFunction $ proposerPayoff reward ;
    outputs   : value ;
    returns   : ;
    // ^ Determines the value


    inputs    : value ;
    feedback  :   ;
    operation : addPayoffs name ;
    outputs   : ;
    returns   : ;
    // ^ Could make sense to make sense to model this in period
    :-----:

    outputs   :  ;
    returns   :  ;

  |]

determineHeadOfChain = [opengame|
    inputs    : chain ;
    feedback  :   ;

    :-----:
    inputs    : chain ;
    feedback  :   ;
    operation : forwardFunction $ determineHead ;
    outputs   : head ;
    returns   : ;
    // ^ Determines the head of the chain

    :-----:

    outputs   : head ;
    returns   :  ;

  |]


proposerPayment name reward = [opengame|

    inputs    : chainNew ;
    feedback  :   ;

    :-----:
    inputs    : chainNew ;
    feedback  :   ;
    operation : forwardFunction proposedCorrect ;
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



----------------------
-- 2 Group Game blocks

-- Group all attesters together
attestersGroupDecision :: Player
                       -> Player
                       ->  OpenGame
                            StochasticStatefulOptic
                            StochasticStatefulContext
                            ('[Kleisli Stochastic (Timer, Relation (Id, Vote), Chain) Int,
                                Kleisli Stochastic (Timer, Relation (Id, Vote), Chain) Int])
                            ('[[DiagnosticInfoBayesian (Timer, Relation (Id, Vote), Chain) Int],
                                [DiagnosticInfoBayesian (Timer, Relation (Id, Vote), Chain) Int]])
                            (Timer, Relation (Id, Vote), Chain, AttesterMap)
                            ()
                            (AttesterMap, Chain)
                            ()
attestersGroupDecision name1 name2 = [opengame|

    inputs    : ticker,chainNew,chainOld, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker, chainNew, chainOld ;
    feedback  :   ;
    operation : attester name1  ;
    outputs   : attested1 ;
    returns   : ;
    // ^ Attester1 makes a decision

    inputs    : ticker, chainNew, chainOld ;
    feedback  :   ;
    operation : attester name2  ;
    outputs   : attested2 ;
    returns   : ;
    // ^ Attester2 makes a decision

    inputs    : [(name1,attested1),(name2,attested2)], attesterHashMapOld ;
    feedback  : ;
    operation : forwardFunction $ uncurry newAttesterMap ;
    outputs   : attesterHashMap ;
    returns   : ;
    // ^ Creates a map of which attester voted for which index

    inputs    : chainNew, [attested1,attested2] ;
    feedback  : ;
    operation : forwardFunction $ uncurry updateVotes ;
    outputs   : chainNewUpdated;
    returns   : ;
    // ^ Updates the chain with the relevant votes


    :-----:

    outputs   : attesterHashMap, chainNewUpdated;
    returns   :  ;
  |]

-- Group payments by attesters
attestersPayment name1 name2 fee = [opengame|

    inputs    : attesterHashMap, chainNew, headId;
    feedback  :   ;

    :-----:
    inputs    : attesterHashMap, chainNew, headId ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 $ attestedCorrect name1 ;
    outputs   : correctAttested1 ;
    returns   : ;
    // ^ This determines whether attester 1 was correct in period (t-1) using the latest hash and the old information

    inputs    : attesterHashMap, chainNew, headId ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 $ attestedCorrect name2 ;
    outputs   : correctAttested2 ;
    returns   : ;
    // ^ This determines whether attester 2 was correct in period (t-1)


    inputs    : correctAttested1 ;
    feedback  :   ;
    operation : updatePayoffAttester name1 fee ;
    outputs   : ;
    returns   : ;
    // ^ Updates the payoff of attester 1 given decision in period (t-1)

    inputs    : correctAttested2 ;
    feedback  :   ;
    operation : updatePayoffAttester name2 fee ;
    outputs   : ;
    returns   : ;
    // ^ Updates the payoff of attester 2 given decision in period (t-1)

        :-----:

    outputs   :  ;
    returns   :  ;
  |]


-------------------
-- 2 Complete games
-------------------

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

-- One round game with proposer who can wait
oneRoundWait p0 p1 a10 a20 a11 a21 reward fee = [opengame|

    inputs    : ticker, delayedTicker, chainOld, attesterHashMapOld  ;
    // ^ chainOld is the old hash
    feedback  :   ;

    :-----:
    inputs    : ticker,delayedTicker,chainOld ;
    feedback  :   ;
    operation : proposerWait p1;
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

-- Repeated game with proposer who can wait
repeatedGameWait  p0 p1 a10 a20 a11 a21 reward fee = [opengame|

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRoundWait p0 p1 a10 a20 a11 a21 reward fee ;
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

-- Two round game with proposer who can wait
-- Follows spec for two players
twoRoundGameWait  p0 p1 p2 a10 a20 a11 a21 a12 a22  reward fee = [opengame|

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRoundWait p0 p1 a10 a20 a11 a21 reward fee ;
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
    operation : oneRoundWait p1 p2 a11 a21 a12 a22 reward fee ;
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

-- Two round game with proposer who can wait
-- Follows spec for two players
-- Tickers are defined externally
twoRoundGameWaitExogTicker  p0 p1 p2 a10 a20 a11 a21 a12 a22  reward fee ticker1 delayedTicker1 ticker2 delayedTicker2= [opengame|

    inputs    :  chainOld, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker1,delayedTicker1, chainOld, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRoundWait p0 p1 a10 a20 a11 a21 reward fee ;
    outputs   : attesterHashMapNew, chainNew, delayedTickerUpdate1 ;
    returns   :  ;

    inputs    : ticker2,delayedTicker2, chainNew, attesterHashMapNew ;
    // NOTE ticker time is ignored here
    feedback  :   ;
    operation : oneRoundWait p1 p2 a11 a21 a12 a22 reward fee ;
    outputs   : attesterHashMapNew2, chainNew2, delayedTickreUpdate2 ;
    returns   :  ;

    :-----:

    outputs   : chainNew2, attesterHashMapNew2 ;
    returns   :  ;
  |]


  
----------------
-- Continuations
-- extract continuation
-- extract continuation
extractContinuation :: StochasticStatefulOptic
                         (Timer, Timer, Chain, M.Map Player Id)
                         ()
                         (Timer, Timer, Chain, M.Map Player Id)
                         ()
                    -> (Timer, Timer, Chain, M.Map Player Id)
                    -> StateT Vector Stochastic ()
extractContinuation (StochasticStatefulOptic v u) (i, j, chain, map) = do
  let x = (i, j, chain, map)
  (z,a) <- ST.lift (v x)
  u z ()

-- extract next state (action)
extractNextState :: StochasticStatefulOptic
                       (Timer, Timer, Chain, M.Map Player Id)
                       ()
                       (Timer,  Timer, Chain , M.Map Player Id)
                       ()
                 -> (Timer, Timer, Chain, M.Map Player Id)
                 -> Stochastic (Timer, Timer, Chain, M.Map Player Id)
extractNextState (StochasticStatefulOptic v _) (i, j, chain, map) = do
  let x = (i, j, chain, map)
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
