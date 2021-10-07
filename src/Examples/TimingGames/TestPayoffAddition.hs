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

module Examples.TimingGames.TestPayoffAddition where

import Engine.Engine
import Preprocessor.Preprocessor
import Examples.Auctions.AuctionSupportFunctions


import           Control.Monad.State  hiding (state,void)
import qualified Control.Monad.State  as ST
import           Data.List



payoffTest True  = 2
payoffTest False = 1

firstRound = [opengame|

    inputs    :  ;
    feedback  :  ;

    :-----:

    inputs    :  ;
    feedback  :   ;
    operation : dependentDecision "proposer" (const [True,False]) ;
    outputs   : sent ;
    returns   : 0;
    // ^ decision whether to send a message or not
    // ^ fix reward to zero; is update where it is evaluated as correct or false

    :-----:

    outputs   : sent;
    returns   :  ;
  |]



secondRound = [opengame|

    inputs    :  sent;
    feedback  :  ;

    :-----:
    inputs    : sent ;
    feedback  :   ;
    operation : forwardFunction $ payoffTest ;
    outputs   : value ;
    returns   : ;


    inputs    : value ;
    feedback  :   ;
    operation : addPayoffs "proposer" ;
    outputs   : ;
    returns   : ;
    :-----:

    outputs   : ;
    returns   :  ;
  |]



bothRounds = [opengame|

    inputs    :  ;
    feedback  :  ;

    :-----:
    inputs    :   ;
    feedback  :   ;
    operation : firstRound ;
    outputs   : value ;
    returns   : ;


    inputs    : value ;
    feedback  :   ;
    operation : secondRound ;
    outputs   : ;
    returns   : ;
    :-----:

    outputs   : ;
    returns   :  ;
  |]


-----------
-- Strategy
strategyTest,strategyTest' :: List '[Kleisli Stochastic () Bool]
strategyTest = pureAction True ::- Nil
strategyTest' = pureAction False ::- Nil

contextTest = StochasticStatefulContext (pure ((),())) (\_ action -> pure ())

eqSingleRound  strat = generateIsEq $ evaluate firstRound strat contextTest
outputSingleRound  strat = generateOutput $ evaluate firstRound strat contextTest


eqBothRounds  strat = generateIsEq $ evaluate bothRounds strat void
outputBothRounds  strat = generateOutput $ evaluate bothRounds strat void
