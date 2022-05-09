{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module WaitTimeEqSpec where

import           Test.Hspec

import           Engine.Engine
import           Examples.TimingGames.TimingGameGraphsAnalysisWait
import           Examples.TimingGames.GraphGames.InternalWait


spec :: Spec
spec = do
  linearChainEq

linearChainEq = describe
   "check equilibrium" $ do
     it "truthful equilibrium" $ do
       shouldBe
         (testEq strategyTupleWait initialContextLinear)
         True
     it "Not sending is not an equilibrium" $ do
       shouldBe
         (testEq strategyTupleWait1 initialContextLinear)
         False
    
  where testEq strategy context= generateEquilibrium $ evaluate (twoRoundGameWait "p0" "p1" "p2" "a10" "a20" "a11" "a21" "a12" "a22" 2 2) strategy context
