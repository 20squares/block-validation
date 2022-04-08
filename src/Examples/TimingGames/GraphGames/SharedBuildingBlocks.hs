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
import           Data.Tuple.Extra (uncurry3)

--------------------------------------------
-- Multiplayer version of the protocol
-- State for each game is a model of a chain

-- TODO Put proposers' decisions also in a map; to have access to earlier player ids
-- TODO For how long will the renumeration of attesters and proposer continue? Is it just for one period? Periods t?


----------
-- A Model
----------


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


oldProposerAddedBlock = [opengame|

    inputs    : chainOld, headOfChainIdT2 ;
    feedback  :   ;

    :-----:
    inputs    : chainOld, headOfChainIdT2 ;
    feedback  :   ;
    operation : forwardFunction $ uncurry wasBlockSent ;
    outputs   : correctSent, headOfChainIdT1 ;
    returns   : ;
    // ^ This determines whether the proposer actually did send a new block in (t-1)
    // ^ It also outputs the head of the chain for period t-1 -- as this is needed in the next period

     :-----:

    outputs   : correctSent, headOfChainIdT1 ;
    returns   :  ;
  |]


  
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

