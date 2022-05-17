{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module ChainEquilibrium
 ( prop_eqForallInitialChains
 , prop_noEqDeviatingProp
 , initialChainLinear)
where 

import           Examples.TimingGames.GraphGames.Internal
import           Examples.TimingGames.Analysis
import           Examples.TimingGames.GraphGames.TypesFunctions
import           Engine.Engine

import           Algebra.Graph.Relation
import           GHC.Generics
import           Generic.Random
import qualified Data.Map.Strict      as M
import           Test.QuickCheck

import Examples.Decision



main = do
  verboseCheck prop_eqForallInitialChains
  verboseCheck (prop_noEqDeviatingProp initialChainLinear)


------------------------------------------------
-- Explore tests of given strategies relative to
-- random starting conditions, i.e. chains

-- draw only positive numbers
genPos :: Gen Int
genPos = abs `fmap` (arbitrary :: Gen Int) `suchThat` (\x -> x > 0  && x < 12)

-- draw a random vertice with increasing number given the state
drawNode :: Id -> Gen (Id,Vote)
drawNode id = (,) <$> choose (id,id) <*> genPos


-- draw an id for the chain at hand
drawId :: Chain -> Gen Id
drawId chain =
  let size = vertexCount chain
      in choose (1,size - 1)

-- create a list of vertices with increasing id
listOfVertices :: Arbitrary (Id,Vote) => Id -> Gen [(Id,Vote)]
listOfVertices id = frequency
  [ (1, return [])
  , (4, (:) <$> drawNode id <*> listOfVertices (id + 1))]

-- first, generate a simple linear path
drawChain :: Gen [(Id,Vote)] -> Gen Chain
drawChain = fmap path


-- checkEq condition on game given an initial chain
eqForallInitialChains initialChain = 
  checkEq initialChain  == True
  where
   checkEq initialChain =  generateEquilibrium $  evaluate (twoRoundGame "p0" "p1" "p2" "a10" "a20" "a11" "a21" "a12" "a22" 2 2 0) strategyTuple context
   context =  StochasticStatefulContext (pure ((),(0,initialChain,3,initialMap))) (\_ _ -> pure ())
   initialMap = M.fromList [("a10",3),("a20",3)]

-- construct testable property
prop_eqForallInitialChains = forAll (drawChain $ listOfVertices 1) eqForallInitialChains

 
------------------------------------------------
-- Explore random strategies different than
-- following the head

-- Strategy for proposer
strategyProposerDeviate :: Id ->  (Kleisli Stochastic (Timer, Chain) (Send Id))
strategyProposerDeviate id = pureAction $ Send id

-- Combining strategies for a single stage
strategyOneRoundDeviate id = strategyProposerDeviate id ::- strategyValidator ::- strategyValidator ::- Nil

-- Combining strategies for several stages
strategyTupleDeviate id = strategyOneRoundDeviate id +:+ strategyOneRound

-- Extract non-equilibrium for proposer
noEqDeviatingProp initialChain id=
  checkEq == False
  where
   checkEq = generateEquilibrium $  evaluate (twoRoundGame "p0" "p1" "p2" "a10" "a20" "a11" "a21" "a12" "a22" 2 2 0) (strategyTupleDeviate id) context
   context =  StochasticStatefulContext (pure ((),(0,initialChain,3,initialMap))) (\_ _ -> pure ())
   initialMap = M.fromList [("a10",3),("a20",3)]


-- construct testable property for proposer strategy
prop_noEqDeviatingProp initialChain = forAll (drawId initialChain) (noEqDeviatingProp initialChain)

