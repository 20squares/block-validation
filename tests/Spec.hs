{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Spec where

import qualified Data.Map.Strict      as M
import Test.Hspec
import Test.QuickCheck

import Engine.Engine
import Examples.TimingGames.TimingGame2MultiPlayersV2


main = do
  hspec $ do spec1
             spec2


-- Tests on the correctness of reward for proposer
spec1 = describe
  "rewardProposer" $ do
    it "new hash building on old one (h|(n+1)=h(n))" $ do
        shouldBe
          (proposedCorrect "test" "Atest")
          True
    it "new hash building on old one" $ do
        shouldBe
          (proposedCorrect "test" "test")
          True
    it "new hash not building on old one (h|(n+1)=h(n-1))" $ do
        shouldBe
          (proposedCorrect "tst" "test")
          False

-- Tests on the correctness of reward for attester
spec2 = describe
  "rewardAttester" $ do
    it "attester point to the correct hash used before (h|(n+1)=h(n) and A(n)=h(n))" $ do
        shouldBe
          (attestedCorrect "attester1" testMap "dcba")
          True
    it "attester points to the incorrect hash used before (h|(n+1)=h(n-1) and A(n)=h(n))" $ do
        shouldBe
          (attestedCorrect "attester1" testMap "cba")
          False
    it "attester points to the correct hash used before (h|(n+1)=h(n-1) and A(n)=h(n-1))" $ do
        shouldBe
          (attestedCorrect "attester2" testMap "eba")
          True
    it "attester points to the incorrect hash used before (h|(n+1)=h(n) and A(n)=h(n-1))" $ do
        shouldBe
          (attestedCorrect "attester2" testMap "dcba")
          False
  where testMap = M.fromList [("attester1","cba"),("attester2","ba")]
