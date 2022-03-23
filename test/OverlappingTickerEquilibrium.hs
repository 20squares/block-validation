{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module OverlappingTickerEquilibrium
  (
    prop_eqForallTickers
  )
where

import           Engine.Engine
import           Examples.TimingGames.GraphGames.InternalOverlappingTicker
import           Examples.TimingGames.ExogenousTicker
import           Examples.TimingGames.GraphGames.TypesFunctions

import qualified Data.Map.Strict      as M
import           Test.QuickCheck

main = do
  verboseCheck prop_eqForallTickers


------------------------------------------------
-- Explore tests of given strategies relative to
-- random starting conditions, i.e. chains

-- draw only positive numbers
genPos :: Gen Int
genPos = abs `fmap` (arbitrary :: Gen Int) `suchThat` (>= 0)

-- draw positive number larger than
genPosLargerThan :: Int -> Gen Int
genPosLargerThan x = abs `fmap` (arbitrary :: Gen Int) `suchThat` (> x)

-- draw tickers with right dependency
drawTickers :: Gen (Int,Int,Int,Int)
drawTickers = do
  t1 <- genPos
  td1 <- genPosLargerThan t1
  t2 <- genPosLargerThan t1
  td2 <- genPosLargerThan t2
  return (t1,td1,t2,td2)

-- checkEq condition on game given an initial chain
eqForallTickers (ticker1,delayedTicker1,ticker2,delayedTicker2) = 
  checkEq ticker1 delayedTicker1 ticker2 delayedTicker2  == True
  where
   checkEq ticker1 delayedTicker1 ticker2 delayedTicker2 =  generateEquilibrium $  evaluate (twoRoundGameWaitExogTicker "p0" "p1" "p2" "a10" "a20" "a11" "a21" "a12" "a22" 2 2 ticker1 delayedTicker1 ticker2 delayedTicker2) strategyTupleWait context
   context =  StochasticStatefulContext (pure ((),(initialChainLinear,initialMap))) (\_ _ -> pure ())
   initialMap = M.fromList [("a10",3),("a20",3)]

-- construct testable property
prop_eqForallTickers = forAll drawTickers eqForallTickers

 
