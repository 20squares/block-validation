{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module GraphSpec where

import           Algebra.Graph.Relation
import           Control.Exception (evaluate)
import           Test.Hspec

import           Examples.TimingGames.GraphGames.Internal


spec :: Spec
spec = do
  chainConstruction
  findVertex
  updateVertex
  findHead

testChain = edges [((1,2),(2,2)),((2,2),(3,1)),((3,1),(4,1))]


chainConstruction = describe
  "chain construction" $ do
     it "is the chain correctly extended" $ do
       shouldBe
        (addToChain testChain 2)
        (overlay testChain (edges [((2,2),(5,0))]))
     it "incorrect extension of chain" $ do
       shouldBe
        (addToChain testChain 2 == overlay testChain (edges [((2,1),(4,0))]))
        False

findVertex = describe
   "find vertex" $ do
     it "find existing vertex" $ do
       shouldBe
         (findVertexById testChain 2)
         (2,2)
     it "does not find not existing id" $ do
       shouldThrow
          (evaluate $ findVertexById testChain 7)
          anyException

updateVertex = describe
   "update vertex according to attester's vote" $ do
      it "correct vertex updated" $ do
        shouldBe
          (attesterChoiceIndex testChain 4)
          (edges [((1,2),(2,2)),((2,2),(3,1)),((3,1),(4,2))])
      it "incorrect vertex updated" $ do
        shouldNotBe
          (attesterChoiceIndex testChain 2)
          (edges [((1,2),(2,2)),((2,2),(3,1)),((3,1),(4,2))])
      it "several vertices are updated" $ do
        shouldBe
          (updateVotes testChain [2,3,4])
          (edges [((1,2),(2,3)),((2,3),(3,2)),((3,2),(4,2))])

findHead = describe
   "find correct head" $ do
     it "find head in a linear chain" $ do
       shouldBe
         (determineHead testChain)
         4
     it "find head in a forked chain" $ do
       shouldBe
         (determineHead (overlay testChain (edges [((2,2),(5,2))])))
         5
     it "find head in a forked chain (2)" $ do
       shouldBe
         (determineHead (overlay testChain (edges [((2,2),(5,0))])))
         4
