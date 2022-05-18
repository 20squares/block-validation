{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module EqSpec where

import           Test.Hspec

import           Engine.Engine
import           Examples.BlockValidation.HonestBehavior
import           Examples.BlockValidation.Representations.Internal


spec :: Spec
spec = do
  linearChainEq

linearChainEq = describe
   "check equilibrium" $ do
     it "truthful equilibrium" $ do
       shouldBe
         (testEq strategyOneEpisode (initialContextLinear "p1" "a11" "a21" 2 2))
         True
  where testEq strategy context= generateEquilibrium $ evaluate (oneEpisode "p0" "p1" "a10" "a20" "a11" "a21" 2 2 0) strategy context
