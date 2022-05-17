{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module EqSpec where

import           Test.Hspec

import           Engine.Engine
import           Examples.TimingGames.Analysis
import           Examples.TimingGames.GraphGames.Internal


spec :: Spec
spec = do
  linearChainEq

linearChainEq = describe
   "check equilibrium" $ do
     it "truthful equilibrium" $ do
       shouldBe
         (testEq strategyTuple initialContextLinear)
         True
   
  where testEq strategy context= generateEquilibrium $ evaluate (twoEpisodeGame "p0" "p1" "p2" "a10" "a20" "a11" "a21" "a12" "a22" 2 2 0) strategy context
