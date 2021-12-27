{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module SpecGraph where

import qualified Data.Map.Strict      as M
import Test.Hspec
import Test.QuickCheck

import Engine.Engine
import Examples.TimingGames.TimingGameGraphsAnalysis
import Examples.TimingGames.GraphGames.Internal


main = do
  hspec $ do chainConstruction



testChain = edges [(0,2),(1,2),(2,1),(3,1)]


chainConstruction = describe
  "chain construction" $ do
     it "is the chain correctly extended" $ do
       shouldBe


{-
-- Tests on the correctness of reward for proposer
spec1 = describe
  "rewardProposer" $ do
    it "new hash building on old one (h|(n+1)=h(n))" $ do
        shouldBe
          (proposedCorrect "test" "Atest")
          True

-- Tests on the correctness of reward for attester
spec2 = describe
  "rewardAttester" $ do
    it "attester point to the correct hash used before (h|(n+1)=h(n) and A(n)=h(n))" $ do
        shouldBe
          (attestedCorrect "attester1" testMap "dcba")
          True
-}
