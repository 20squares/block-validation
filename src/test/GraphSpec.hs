{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module GraphSpec where


import           BlockValidation.Representations.TypesFunctions

import           Algebra.Graph.Relation
import           Control.Exception (evaluate)
import qualified Data.Map.Strict      as M
import qualified Data.Set             as S
import           Test.Hspec



spec :: Spec
spec = do
  chainConstruction
  findVertex
  updateVertex
  attested
  proposed
  proposerAlternatives
  findHead

testChain = edges [((1,2),(2,2)),((2,2),(3,1)),((3,1),(4,1))]

testChain2 = edges [((1,2),(2,2)),((1,2),(4,0)),((2,2),(3,4)),((3,4),(5,0))]

testChain3 = edges [((1,2),(2,2)),((1,2),(4,0)),((2,2),(3,4)),((3,4),(5,2))]

testChain4 = edges [((1,2),(2,2)),((1,2),(4,7)),((2,2),(3,4)),((3,4),(5,0))]

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
   "update vertex according to validator's vote" $ do
      it "correct vertex updated" $ do
        shouldBe
          (validatorChoiceIndex testChain 4)
          (edges [((1,2),(2,2)),((2,2),(3,1)),((3,1),(4,2))])
      it "incorrect vertex updated" $ do
        shouldNotBe
          (validatorChoiceIndex testChain 2)
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
         (attestedCorrect "p1" testMap testChain (S.singleton 4))
         True
     it "attested correctly non-linear chain" $ do
       shouldBe
         (attestedCorrect "p1" testMap (overlay testChain (edges [((2,2),(5,4))])) (S.singleton 5))
         True
     it "attested incorrectly non-linear chain" $ do
       shouldBe
         (attestedCorrect "p2" testMap (overlay testChain (edges [((2,2),(5,4))])) (S.singleton 5))
         False
     it "attested correctly non-linear chain fork" $ do
       shouldBe
         (attestedCorrect "p3" testMap (overlay testChain (edges [((2,2),(5,4))])) (S.singleton 5))
         True

proposed = describe
   "proposed correctly" $ do
     it "proposed correctly linear chain" $ do
       shouldBe
         (proposedCorrect True testChain)
         True
     it "proposed incorrectly forked chain" $ do
       shouldBe
         (proposedCorrect True ((overlay testChain (edges [((2,2),(5,4))]))))
         False
     it "proposed incorrectly forked chain (2)" $ do
       shouldBe
         (proposedCorrect True ((overlay testChain (edges [((2,2),(5,4))]))))
         False
     it "proposed correctly forked chain " $ do
       shouldBe
         (proposedCorrect True ((overlay testChain (edges [((2,2),(5,4)),((5,4),(6,3))]))))
         True
     it "proposed correctly forked chain (2)" $ do
        shouldBe
         (proposedCorrect True testChain2)
         False

proposerAlternatives = describe
    "proposer's alternatives are constructed correctly" $ do
      it "correct alternatives linear chain" $ do
        shouldBe
          (alternativesProposer (0,testChain))
          [DoNotSend, Send 1, Send 2, Send 3, Send 4]
      it "correct new chain is constructed when send decision" $ do
        shouldBe
          (addToChainWait testChain (Send 4))
          (path [(1,2),(2,2),(3,1),(4,1),(5,0)])
      it "correct new chain is constructed when no-send decision" $ do
        shouldBe
          (addToChainWait testChain (DoNotSend))
          (path [(1,2),(2,2),(3,1),(4,1)])



findHead = describe
   "find-correct-head" $ do
     it "find head in a linear chain" $ do
       shouldBe
         (determineHead testChain)
         (S.singleton 4)
     it "find head in a linear chain (2)" $ do
       shouldBe
         (determineHead testChain2)
         (S.singleton 5)
     it "find head in a linear chain (3)" $ do
       shouldBe
         (determineHead testChain3)
         (S.singleton 5)
     it "find head in a linear chain (4)" $ do
       shouldBe
         (determineHead testChain4)
         (S.singleton 4)
     it "find head in a forked chain" $ do
       shouldBe
         (determineHead (overlay testChain (edges [((2,2),(5,2))])))
         (S.fromList [4,5])
     it "find head in a forked chain (2)" $ do
       shouldBe
         (determineHead (overlay testChain (edges [((2,2),(5,0))])))
         (S.singleton 4)

