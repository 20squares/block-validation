{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module BlockValidation.Representations.Internal where


import           Engine.Engine
import           Preprocessor.Preprocessor
import           BlockValidation.Representations.TypesFunctions
import           BlockValidation.Representations.SharedBuildingBlocks


import           Algebra.Graph.Relation
import           Data.Tuple.Extra (uncurry3)

--------------------------------------------
-- Multiplayer version of the protocol
-- State for each game is a model of a chain
-- Proposer has the possibility to not add to the chain

-- TODO For how long will the renumeration of validators and proposer continue? Is it just for one period? Periods t?


----------
-- A Model
----------

----------------------
-- 1 Group Game blocks

-- Group all validators together
validatorsGroupDecision name1 name2 = [opengame|

    inputs    : ticker,chainNew,chainOld, validatorsHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker, chainNew, chainOld ;
    feedback  :   ;
    operation : validator name1  ;
    outputs   : attested1 ;
    returns   : ;
    // ^ Validator1 makes a decision

    inputs    : ticker, chainNew, chainOld ;
    feedback  :   ;
    operation : validator name2  ;
    outputs   : attested2 ;
    returns   : ;
    // ^ Validator2 makes a decision

    inputs    : [(name1,attested1),(name2,attested2)], validatorsHashMapOld ;
    feedback  : ;
    operation : forwardFunction $ uncurry newValidatorMap ;
    outputs   : validatorHashMap ;
    returns   : ;
    // ^ Creates a map of which validator voted for which index

    inputs    : chainNew, [attested1,attested2] ;
    feedback  : ;
    operation : forwardFunction $ uncurry updateVotes ;
    outputs   : chainNewUpdated;
    returns   : ;
    // ^ Updates the chain with the relevant votes


    :-----:

    outputs   : validatorHashMap, chainNewUpdated;
    returns   :  ;
  |]

-- Group payments by validators
validatorsPayment name1 name2 fee = [opengame|

    inputs    : validatorHashMap, chainNew, headId;
    feedback  :   ;

    :-----:
    inputs    : validatorHashMap, chainNew, headId ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 $ attestedCorrect name1 ;
    outputs   : correctAttested1 ;
    returns   : ;
    // ^ This determines whether validator 1 was correct in period (t-1) using the latest hash and the old information

    inputs    : validatorHashMap, chainNew, headId ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 $ attestedCorrect name2 ;
    outputs   : correctAttested2 ;
    returns   : ;
    // ^ This determines whether validator 2 was correct in period (t-1)


    inputs    : correctAttested1 ;
    feedback  :   ;
    operation : updatePayoffValidator name1 fee ;
    outputs   : ;
    returns   : ;
    // ^ Updates the payoff of validator 1 given decision in period (t-1)

    inputs    : correctAttested2 ;
    feedback  :   ;
    operation : updatePayoffValidator name2 fee ;
    outputs   : ;
    returns   : ;
    // ^ Updates the payoff of validator 2 given decision in period (t-1)

        :-----:

    outputs   :  ;
    returns   :  ;
  |]

-------------------
-- 2 Complete games
-------------------

-- One episode game with proposer who can wait
oneEpisode p0 p1 a10 a20 a11 a21 reward fee delayTreshold = [opengame|

    inputs    : ticker, chainOld, headOfChainIdT2, validatorsHashMapOld  ;
    // ^ chainOld is the old hash
    feedback  :   ;

    :-----:
    inputs    : ticker, chainOld ;
    feedback  :   ;
    operation : proposer p1 delayTreshold ;
    outputs   : chainNew ;
    returns   : ;
    // ^ Proposer makes a decision, a new hash is proposed

    inputs    : ticker,chainNew,chainOld, validatorsHashMapOld;
    feedback  :   ;
    operation : validatorsGroupDecision a11 a21 ;
    outputs   : validatorHashMapNew, chainNewUpdated ;
    returns   :  ;
    // ^ Validators make a decision

    inputs    : chainNewUpdated ;
    feedback  :   ;
    operation : determineHeadOfChain ;
    outputs   : headOfChainId ;
    returns   : ;
    // ^ Determines the head of the chain

    inputs    : validatorsHashMapOld, chainNewUpdated, headOfChainId ;
    feedback  :   ;
    operation : validatorsPayment a10 a20 fee ;
    outputs   : ;
    returns   : ;
    // ^ Determines whether validators from period (t-1) were correct and get rewarded

    inputs    : chainOld, headOfChainIdT2 ;
    feedback  :   ;
    operation : oldProposerAddedBlock ;
    outputs   : blockAddedInT1, headOfChainIdT1;
    returns   : ;
    // ^ This determines whether the proposer from period (t-1) did actually add a block or not

    inputs    : blockAddedInT1, chainNewUpdated ;
    feedback  :   ;
    operation : proposerPayment p0 reward ;
    outputs   :  ;
    returns   :  ;
    // ^ This determines whether the proposer from period (t-1) was correct and triggers payments accordingly

    :-----:

    outputs   : chainNewUpdated,  headOfChainIdT1,  validatorHashMapNew  ;
    returns   :  ;
  |]


-- One episode game with proposer who can wait; allows for a different chain being observed by proposer
-- and validators. Useful for analysis of attack
oneEpisodeAttack p0 p1 a10 a20 a11 a21 reward fee delayTreshold = [opengame|

    inputs    : ticker, chainOld, headOfChainIdT2, validatorsHashMapOld, chainManipulated ;
    // ^ chainOld is the old hash
    feedback  :   ;

    :-----:
    inputs    : ticker, chainOld ;
    feedback  :   ;
    operation : proposer p1 delayTreshold ;
    outputs   : chainNew ;
    returns   : ;
    // ^ Proposer makes a decision, a new hash is proposed

     inputs    : chainNew, chainManipulated ;
    feedback  :   ;
    operation : mergeChain ;
    outputs   : mergedChain ;
    returns   : ;
    // ^ Merges the two chains into a new chain for the validators

    inputs    : ticker,mergedChain,chainOld, validatorsHashMapOld;
    feedback  :   ;
    operation : validatorsGroupDecision a11 a21 ;
    outputs   : validatorHashMapNew, chainNewUpdated ;
    returns   :  ;
    // ^ Validators make a decision

    inputs    : chainNewUpdated ;
    feedback  :   ;
    operation : determineHeadOfChain ;
    outputs   : headOfChainId ;
    returns   : ;
    // ^ Determines the head of the chain

    inputs    : validatorsHashMapOld, chainNewUpdated, headOfChainId ;
    feedback  :   ;
    operation : validatorsPayment a10 a20 fee ;
    outputs   : ;
    returns   : ;
    // ^ Determines whether validators from period (t-1) were correct and get rewarded

    inputs    : chainOld, headOfChainIdT2 ;
    feedback  :   ;
    operation : oldProposerAddedBlock ;
    outputs   : blockAddedInT1, headOfChainIdT1;
    returns   : ;
    // ^ This determines whether the proposer from period (t-1) did actually add a block or not

    inputs    : blockAddedInT1, chainNewUpdated ;
    feedback  :   ;
    operation : proposerPayment p0 reward ;
    outputs   :  ;
    returns   :  ;
    // ^ This determines whether the proposer from period (t-1) was correct and triggers payments accordingly

    :-----:

    outputs   : chainNewUpdated,  headOfChainIdT1,  validatorHashMapNew  ;
    returns   :  ;
  |]



-- Two episode game with proposer who can wait
-- Follows spec for two players
twoEpisodeGame  p0 p1 p2 a10 a20 a11 a21 a12 a22  reward fee delayTreshold= [opengame|

    inputs    : ticker, chainOld, headOfChainIdT2, validatorsHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker,chainOld, headOfChainIdT2, validatorsHashMapOld ;
    feedback  :   ;
    operation : oneEpisode p0 p1 a10 a20 a11 a21 reward fee delayTreshold ;
    outputs   : chainNew,  headOfChainIdT1, validatorHashMapNew  ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    inputs    : ticker, chainNew, headOfChainIdT1, validatorHashMapNew ;
    // NOTE ticker time is ignored here
    feedback  :   ;
    operation : oneEpisode p1 p2 a11 a21 a12 a22 reward fee delayTreshold ;
    outputs   : chainNew2, headOfChainIdT, validatorHashMapNew2 ;
    returns   :  ;

    inputs    : tickerNew;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew2;
    returns   : ;



    :-----:

    outputs   : tickerNew2, chainNew2, headOfChainIdT, validatorHashMapNew2 ;
    returns   :  ;
  |]

 

-- Repeated game with proposer who can wait
repeatedGame  p0 p1 a10 a20 a11 a21 reward fee delayTreshold  = [opengame|

    inputs    : ticker, chainOld, headOfChainIdT2, validatorsHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker, chainOld, headOfChainIdT2, validatorsHashMapOld ;
    feedback  :   ;
    operation : oneEpisode p0 p1 a10 a20 a11 a21 reward fee delayTreshold ;
    outputs   : chainNew, headOfChainIdT1, validatorHashMapNew  ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    :-----:

    outputs   : tickerNew, chainNew, headOfChainIdT1, validatorHashMapNew ;
    returns   :  ;
  |]




