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
import           Examples.TimingGames.GraphGames.SharedBuildingBlocks

import           Algebra.Graph.Relation
import           Control.Monad.State  hiding (state,void)
import qualified Control.Monad.State  as ST
import qualified Data.Map.Strict      as M
import           Data.NumInstances.Tuple
-- NOTE ^^ this is for satisfying the class restrictions of Algebra.Graph.Relation
import qualified Data.Set             as S
import           Data.Tuple.Extra (uncurry3)


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
    operation : dependentDecision name alternativesProposer;
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

    outputs   : messageChain ;
    // ^ newchain (if timer allows otherwise old chain), update on delayedticker, decisionProposer
    returns   :  ;
  |]



  

-------------------
-- 2 Complete games
-------------------

-- One round game with proposer who can wait
oneRoundWait p0 p1 a10 a20 a11 a21 reward fee = [opengame|

    inputs    : ticker, delayedTicker, chainOld, attesterHashMapOld  ;
    // ^ chainOld is the old hash
    feedback  :   ;

    :-----:
    inputs    : ticker,delayedTicker,chainOld ;
    feedback  :   ;
    operation : proposerWait p1;
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

    inputs    : chainNewUpdated ;
    feedback  :   ;
    operation : proposerPayment p0 reward ;
    outputs   :  ;
    returns   : ;
    // ^ This determines whether the proposer from period (t-1) was correct and triggers payments accordingly

    :-----:

    outputs   : attesterHashMapNew, chainNewUpdated ;
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
    outputs   : attesterHashMapNew, chainNew ;
    returns   :  ;

    inputs    : ticker2,delayedTicker2, chainNew, attesterHashMapNew ;
    // NOTE ticker time is ignored here
    feedback  :   ;
    operation : oneRoundWait p1 p2 a11 a21 a12 a22 reward fee ;
    outputs   : attesterHashMapNew2, chainNew2 ;
    returns   :  ;

    :-----:

    outputs   : chainNew2, attesterHashMapNew2 ;
    returns   :  ;
  |]


  
