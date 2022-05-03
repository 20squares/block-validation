{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Examples.TimingGames.GraphGames.InternalWait where


import           Engine.Engine
import           Preprocessor.Preprocessor
import           Examples.TimingGames.GraphGames.TypesFunctions
import           Examples.TimingGames.GraphGames.SharedBuildingBlocks


--------------------------------------------
-- Multiplayer version of the protocol
-- State for each game is a model of a chain
-- Proposer has the possibility to not add to the chain

-- TODO Put proposers' decisions also in a map; to have access to earlier player ids
-- TODO For how long will the renumeration of attesters and proposer continue? Is it just for one period? Periods t?


----------
-- A Model
----------

---------------------
-- 1 Game blocks

-- Given the decision by the proposer to either wait or to send a head
-- the "new" chain is created -- which means either the same as before
-- or the actually appended version
addBlockWait = [opengame|

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

-- One round game with proposer who can wait
oneRoundWait p0 p1 a10 a20 a11 a21 reward fee = [opengame|

    inputs    : ticker, delayedTicker, chainOld, headOfChainIdT2, attesterHashMapOld  ;
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

    outputs   : delayedTickerUpdate,chainNewUpdated,  headOfChainIdT1,  attesterHashMapNew  ;
    returns   :  ;
  |]



-- Repeated game with proposer who can wait
repeatedGameWait  p0 p1 a10 a20 a11 a21 reward fee = [opengame|

    inputs    : ticker,delayedTicker, chainOld, headOfChainIdT2, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker,delayedTicker, chainOld, headOfChainIdT2, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRoundWait p0 p1 a10 a20 a11 a21 reward fee ;
    outputs   : attesterHashMapNew, chainNew, headOfChainIdT1, delayedTickerUpdate ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    :-----:

    outputs   : tickerNew, delayedTickerUpdate, chainNew, headOfChainIdT1, attesterHashMapNew ;
    returns   :  ;
  |]



-- Two round game with proposer who can wait
-- Follows spec for two players
twoRoundGameWait  p0 p1 p2 a10 a20 a11 a21 a12 a22  reward fee = [opengame|

    inputs    : ticker,delayedTicker, chainOld, headOfChainIdT2, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker,delayedTicker, chainOld, headOfChainIdT2, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRoundWait p0 p1 a10 a20 a11 a21 reward fee ;
    outputs   : delayedTickerUpdate, chainNew,  headOfChainIdT1, attesterHashMapNew  ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    inputs    : ticker,delayedTicker, chainNew, headOfChainIdT1, attesterHashMapNew ;
    // NOTE ticker time is ignored here
    feedback  :   ;
    operation : oneRoundWait p1 p2 a11 a21 a12 a22 reward fee ;
    outputs   : delayedTickerUpdate2, chainNew2, headOfChainIdT, attesterHashMapNew2 ;
    returns   :  ;

    inputs    : tickerNew;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew2;
    returns   : ;



    :-----:

    outputs   : tickerNew2, delayedTickerUpdate2, chainNew2, headOfChainIdT, attesterHashMapNew2 ;
    returns   :  ;
  |]


