{-# LANGUAGE DataKinds #-}
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

import           Examples.TimingGames.GraphGames.Internal
import           Examples.TimingGames.TimingGameGraphsAnalysis
import           Engine.Engine

import           Algebra.Graph.Relation
import           GHC.Generics
import           Generic.Random
import qualified Data.Map.Strict      as M
import           Test.QuickCheck

import Examples.Decision


main = undefined



------------------------------------------------
-- Explore tests of given strategies relative to
-- random starting conditions, i.e. chains

-- draw a random vertice with increasing number given the state
drawNode :: Id -> Gen (Id,Vote)
drawNode id = (,) <$> choose (id,id) <*> arbitrary

-- create a list of vertices with increasing id
listOfVertices :: Arbitrary (Id,Vote) => Id -> Gen [(Id,Vote)]
listOfVertices id = frequency
  [ (1, return [])
  , (4, (:) <$> drawNode id <*> listOfVertices (id + 1))]

-- first, generate a simple linear path
drawChain :: Gen [(Id,Vote)] -> Gen Chain
drawChain = fmap path



test1 initialChain =  generateEquilibrium $  evaluate (twoRoundGame "p0" "p1" "p2" "a10" "a20" "a11" "a21" "a12" "a22" 2 2) strategyTuple context
  where context =  StochasticStatefulContext (pure ((),(0,0,test2,initialMap))) (\_ _ -> pure ())
        initialMap = M.fromList [("a10",3),("a20",3)]

test2 :: Chain
test2 = path [(1,2),(2,2),(3,2)] 

--test3 initialChain = foldrL and True (test1 initialChain) 
--foldrL and True $

-- fmap into Bool, fold into Bool and then extract?
prop_eqForallInitialChains initialChain =
  True  == True
  where context =  StochasticStatefulContext (pure ((),(0,0,initialChain,initialMap))) (\_ _ -> pure ())
        initialMap = M.fromList [("a10",3),("a20",3)]
 






------------------------------------------------
-- Explore random strategies different than
-- following the head


