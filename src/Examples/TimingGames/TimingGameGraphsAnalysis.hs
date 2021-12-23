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

module Examples.TimingGames.TimingGameGraphsAnalysis where

import           Engine.Engine
import           Preprocessor.Preprocessor

import           Examples.TimingGames.GraphGames.Internal
-----------
-- Analysis

eq iterator strat initialState = generateIsEq $ evaluate (repeatedGame  2 2) strat (contextCont iterator strat initialState)

showOutput iterator strat initialState = generateOutput $ evaluate (repeatedGame  2 2) strat (contextCont iterator strat initialState)



strategyProposer :: Kleisli Stochastic Int Send
strategyProposer = pureAction Send

strategyProposer' :: Kleisli Stochastic Int Send
strategyProposer' = pureAction DoNotSend

strategyAttester :: Kleisli Stochastic (Int, String, String) String
strategyAttester = Kleisli (\(_, newHash, _) -> pure newHash)

strategyAttester' :: Kleisli Stochastic (Int, String, String) String
strategyAttester' = Kleisli (\(_, _, oldHash) -> pure oldHash)

strategyAttester'' :: Kleisli Stochastic (Int, String, String) String
strategyAttester'' = Kleisli (\(_, newHash, oldHash) -> uniformDist [newHash,oldHash])



strategyTuple = strategyProposer ::- strategyAttester ::- Nil

strategyTuple2 = strategyProposer' ::- strategyAttester' ::- Nil

strategyTuple3 = strategyProposer' ::- strategyAttester ::- Nil

strategyTuple4 = strategyProposer ::- strategyAttester' ::- Nil

strategyTuple5 = strategyProposer' ::- strategyAttester'' ::- Nil

strategyTuple6 = strategyProposer ::- strategyAttester'' ::- Nil
-- Start with the situation of one attester and one proposer
initialState = (0,0,"a","")

-------------------
-- Scenarios Tested

{-
-- NOTE Both players truthtelling is also an equilibrium
eq 2 strategyTuple (1,0,"a","")
eq 2 strategyTuple (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple (1,0,"a","a")
eq 2 strategyTuple (0,0,"a","a")


-- NOTE this is a scenario where both players coordinate against the true value; but the strategy of the attester is irrelevant here as he only sees the same information
eq 2 strategyTuple2 (1,0,"a","")
eq 2 strategyTuple2 (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple2 (1,0,"a","a")
eq 2 strategyTuple2 (0,0,"a","a")

-- NOTE proposer not telling the truth but attester is, is also an equilibrium. Makes sense as the attester can only attest what is there
eq 2 strategyTuple3 (1,0,"a","")
eq 2 strategyTuple3 (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple3 (1,0,"a","a")
eq 2 strategyTuple3 (0,0,"a","a")

-- NOTE proposer telling the truth but attester is not, is _not_ an equilibrium.
eq 2 strategyTuple4 (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple4 (0,0,"a","a")

-- NOTE the behavior above depends on the state!
eq 2 strategyTuple4 (1,0,"a","")
eq 2 strategyTuple4 (1,0,"a","a")
-}
