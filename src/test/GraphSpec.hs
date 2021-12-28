{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module GraphSpec where

import           Algebra.Graph.Relation
import           Control.Exception (evaluate)
import qualified Data.Map.Strict      as M
import           Test.Hspec

import           Examples.TimingGames.GraphGames.Internal


spec :: Spec
spec = do
  chainConstruction
  findVertex
  updateVertex
  attested
  proposed
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

-- construct test map for individual votes
testMap = M.fromList [("p1",2),("p2",4),("p3",5)]

attested = describe
   "attested correctly" $ do
     it "attested correctly linear chain" $ do
       shouldBe
         (attestedCorrect "p1" testMap testChain 4)
         True
     it "attested correctly non-linear chain" $ do
       shouldBe
         (attestedCorrect "p1" testMap (overlay testChain (edges [((2,1),(5,4))])) 5)
         True
     it "attested incorrectly non-linear chain" $ do
       shouldBe
         (attestedCorrect "p2" testMap (overlay testChain (edges [((2,1),(5,4))])) 5)
         False
     it "attested correctly non-linear chain fork" $ do
       shouldBe
         (attestedCorrect "p3" testMap (overlay testChain (edges [((2,1),(5,4))])) 5)
         True

proposed = describe
   "proposed correctly" $ do
     it "proposed correctly linear chain" $ do
       shouldBe
         (proposedCorrect testChain 4)
         True
     it "proposed incorrectly forked chain" $ do
       shouldBe
         (proposedCorrect ((overlay testChain (edges [((2,1),(5,4))]))) 5)
         False
     it "proposed incorrectly forked chain (2)" $ do
       shouldBe
         (proposedCorrect ((overlay testChain (edges [((2,1),(5,4))]))) 3)
         False
     it "proposed incorrectly forked chain (3)" $ do
       shouldBe
         (proposedCorrect ((overlay testChain (edges [((2,1),(5,4))]))) 2)
         False
     it "proposed correctly forked chain " $ do
       shouldBe
         (proposedCorrect ((overlay testChain (edges [((2,1),(5,4)),((5,4),(6,3))]))) 6)
         True





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


testPastHeadId chain = vertexCount chain - 2

pastHead chain pastHeadId = findVertexById chain pastHeadId

currentHead chain headOfChain = findVertexById chain headOfChain

onPathElems currentHead chain = preSet currentHead (closure chain)


testChain2 = (overlay testChain (edges [((2,1),(5,4)),((5,4),(6,3))]))
