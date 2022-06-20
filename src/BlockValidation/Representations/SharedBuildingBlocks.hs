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

module BlockValidation.Representations.SharedBuildingBlocks where


import           Engine.Engine
import           Preprocessor.Preprocessor
import           BlockValidation.Representations.TypesFunctions

import           Algebra.Graph.Relation

--------------------------------------------
-- Multiplayer version of the protocol
-- State for each game is a model of a chain


----------
-- A Model
----------


-- Given the decision by the proposer to either wait or to send a head, creates a new chain.
-- Which means either the old chain is copied as before or the chain is actually appended by a new block.
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



-- Given a new chain proposed and the old chain from (t-1), `validator` then decides which node to attest as the head.
validator name = [opengame|

    inputs    : chainNew,chainOld ;
    feedback  :  ;

    :-----:
    inputs    : chainNew,chainOld ;
    feedback  :   ;
    operation : dependentDecision name (\(chainNew, chainOld) -> [1, vertexCount chainNew]) ;
    outputs   : attestedIndex ;
    returns   : 0 ;
    // ^ NOTE the payoff for the validator comes from the next period

    :-----:

    outputs   : attestedIndex ;
    returns   :  ;
  |]



-- Given the old chain from (t-1), decides to append the block to a node or not to append.
-- Conditional on that decision, a new chain is created.
proposer  name = [opengame|

    inputs    : chainOld;
    feedback  :   ;

    :-----:
    inputs    : chainOld ;
    feedback  :   ;
    operation : dependentDecision name  alternativesProposer;
    outputs   : decisionProposer ;
    returns   : 0;
    // ^ NOTE fix reward to zero; it is later updated where it is evaluated as correct or false

    inputs    : chainOld, decisionProposer ;
    feedback  :   ;
    operation : addBlock ;
    outputs   : chainNew;
    returns   : ;

    :-----:

    outputs   : chainNew ;
    returns   :  ;
  |]


-- Update the payoff of the validator conditional on the correctness of his action
updatePayoffValidator name fee  = [opengame|
    inputs    : bool ;
    feedback  :   ;

    :-----:
    inputs    : bool ;
    feedback  :   ;
    operation : forwardFunction $ validatorPayoff fee ;
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

-- Given a chain, produces the head of the current chain
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

-- Given the old chain from (t-1) and the head of the chain from (t-2), determines whether the proposer
-- actually did send a new block in (t-1). It also outputs the head of the chain for period (t-1) -- as this is needed in the next period. 
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


-- Merge two chains -- needed when there is an attack
mergeChain :: (Ord a, Show a) =>
                    OpenGame
                      StochasticStatefulOptic
                      StochasticStatefulContext
                        ('[])
                        ('[])
                        (Relation a, Relation a)
                        ()
                        (Relation a)
                        ()
mergeChain = [opengame|

    inputs    : chain1, chain2 ;
    feedback  :   ;

    :-----:
    inputs    : chain1, chain2 ;
    feedback  :   ;
    operation : forwardFunction $ uncurry $ overlay ;
    outputs   : mergedChain ;
    returns   : ;
    :-----:

    outputs   : mergedChain ;
    returns   :  ;
  |]

