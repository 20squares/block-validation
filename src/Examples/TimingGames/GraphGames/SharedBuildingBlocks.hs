{-# LANGUAGE DatatypeContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Examples.TimingGames.GraphGames.SharedBuildingBlocks where


import           Engine.Engine
import           Preprocessor.Preprocessor
import           Examples.TimingGames.GraphGames.TypesFunctions

import           Algebra.Graph.Relation

--------------------------------------------
-- Multiplayer version of the protocol
-- State for each game is a model of a chain

-- TODO Put proposers' decisions also in a map; to have access to earlier player ids
-- TODO For how long will the renumeration of attesters and proposer continue? Is it just for one period? Periods t?
-- TODO All the components should be here


----------
-- A Model
----------


-- Given the decision by the proposer to either wait or to send a head
-- the "new" chain is created -- which means either the same as before
-- or the actually appended version
addBlock = [opengame|

    inputs    : chainOld, chosenIdOrWait ;
    feedback  :   ;

    :-----:
    inputs    : chainOld, chosenIdOrWait ;
    feedback  :   ;
    operation : forwardFunction $ uncurry addToChainWait ;
    outputs   : chainNew ;
    returns   : ;

    :-----:

    outputs   : chainNew ;
    returns   :          ;
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
    // ^ the attester picks a vertex to vote on -- as the head of the chain
    // ^ NOTE the payoff for the attester comes from the next period

    :-----:

    outputs   : attestedIndex ;
    returns   :  ;
  |]



-- A proposer observes the ticker and decides to append the block to a node OR not
-- In other words, the proposer can wait to append the block
-- The _delayedTicker_ is an additional parameter fed into the game, 
proposer  name delayThreshold = [opengame|

    inputs    : ticker, chainOld;
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
    operation : addBlock ;
    outputs   : chainNew;
    returns   : ;
    // ^ creates new hash at t=0

    inputs    : ticker, chainOld, chainNew ;
    feedback  :   ;
    operation : forwardFunction $ delayMessage delayThreshold ;
    outputs   : messageChain ;
    returns   : ;
    // ^ for a given timer, determines whether the block is decisionProposer or not

    :-----:

    outputs   : messageChain ;
    // ^ newchain (if timer allows otherwise old chain), update on delayedticker, decisionProposer
    returns   :  ;
  |]


-- Update the payoff of the attester conditional on the correctness of his action
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

-- Update the payoff of the proposer conditional on the correctness of his decision
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

-- Determines the head of the chain
determineHeadOfChain = [opengame|
    inputs    : chain ;
    feedback  :   ;

    :-----:
    inputs    : chain ;
    feedback  :   ;
    operation : forwardFunction $ determineHead ;
    outputs   : head ;
    returns   : ;
    :-----:

    outputs   : head ;
    returns   :  ;

  |]

-- Determines whether the proposer actually did send a new block in (t-1).
-- It also outputs the head of the chain for period (t-1) -- as this is needed in the next period
oldProposerAddedBlock = [opengame|

    inputs    : chainOld, headOfChainIdT2 ;
    feedback  :   ;

    :-----:
    inputs    : chainOld, headOfChainIdT2 ;
    feedback  :   ;
    operation : forwardFunction $ uncurry wasBlockSent ;
    outputs   : correctSent, headOfChainIdT1 ;
    returns   : ;
     :-----:

    outputs   : correctSent, headOfChainIdT1 ;
    returns   :  ;
  |]


-- Determines whether the proposer was correct and triggers payment accordingly
proposerPayment name reward = [opengame|

    inputs    : blockAddedInT1, chainNew ;
    feedback  :   ;

    :-----:
    inputs    : blockAddedInT1, chainNew ;
    feedback  :   ;
    operation : forwardFunction $ uncurry proposedCorrect ;
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



