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
import           Examples.TimingGames.GraphGames.TypesFunctions
import           Examples.TimingGames.GraphGames.SharedBuildingBlocks


import           Algebra.Graph.Relation
import           Data.Tuple.Extra (uncurry3)

--------------------------------------------
-- Multiplayer version of the protocol
-- State for each game is a model of a chain
-- Proposer has the possibility to not add to the chain

-- TODO For how long will the renumeration of attesters and proposer continue? Is it just for one period? Periods t?


----------
-- A Model
----------

----------------------
-- 1 Group Game blocks

-- Group all attesters together
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

-- One round game with proposer who can wait
oneRound p0 p1 a10 a20 a11 a21 reward fee delayTreshold = [opengame|

    inputs    : ticker, chainOld, headOfChainIdT2, attesterHashMapOld  ;
    // ^ chainOld is the old hash
    feedback  :   ;

    :-----:
    inputs    : ticker, chainOld ;
    feedback  :   ;
    operation : proposer p1 delayTreshold ;
    outputs   : chainNew ;
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

    outputs   : chainNewUpdated,  headOfChainIdT1,  attesterHashMapNew  ;
    returns   :  ;
  |]



-- Repeated game with proposer who can wait
repeatedGame  p0 p1 a10 a20 a11 a21 reward fee delayTreshold  = [opengame|

    inputs    : ticker, chainOld, headOfChainIdT2, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker, chainOld, headOfChainIdT2, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRound p0 p1 a10 a20 a11 a21 reward fee delayTreshold ;
    outputs   : chainNew, headOfChainIdT1, attesterHashMapNew  ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    :-----:

    outputs   : tickerNew, chainNew, headOfChainIdT1, attesterHashMapNew ;
    returns   :  ;
  |]



-- Two round game with proposer who can wait
-- Follows spec for two players
twoRoundGame  p0 p1 p2 a10 a20 a11 a21 a12 a22  reward fee delayTreshold= [opengame|

    inputs    : ticker, chainOld, headOfChainIdT2, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker,chainOld, headOfChainIdT2, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRound p0 p1 a10 a20 a11 a21 reward fee delayTreshold ;
    outputs   : chainNew,  headOfChainIdT1, attesterHashMapNew  ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    inputs    : ticker, chainNew, headOfChainIdT1, attesterHashMapNew ;
    // NOTE ticker time is ignored here
    feedback  :   ;
    operation : oneRound p1 p2 a11 a21 a12 a22 reward fee delayTreshold ;
    outputs   : chainNew2, headOfChainIdT, attesterHashMapNew2 ;
    returns   :  ;

    inputs    : tickerNew;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew2;
    returns   : ;



    :-----:

    outputs   : tickerNew2, chainNew2, headOfChainIdT, attesterHashMapNew2 ;
    returns   :  ;
  |]


