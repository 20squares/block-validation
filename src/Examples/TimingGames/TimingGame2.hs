{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Examples.TimingGames.TimingGame2 where

-- TODO Test that the payoff version actually works
-- TODO Testing of equilibrium
-- TODO Check the initial state conditions make sense
-- DONE Can we remodel this game as to use the state hack as well?
-- DONE Do we need more attesters to make that model relevant?
-- DONE What is the payoff for the sender?
-- DONE Check strategies and explore game

{--

We simplify the Proof-of-Stake (PoS) Ethereum protocol:

Time is divided in slots of 12 seconds.

A block proposer is expected to send their block B

at t=0
seconds into the first slot.
At t=4
seconds into the slot, an attester is expected to publish their view of the chain v: the hash of B if it is available, or an empty vote ∅
otherwise.
At t=12
seconds into the slot (i.e., t=0 into the next slot), the game is repeated: a block proposer is expected to send a block B′, which contains v if v
was received in time by the proposer.
The attester is rewarded if their vote is included in block B′
and is correct, i.e., voted ∅ if B′ did not build on B, and hash(B)

    otherwise.

Propagation times follow some distribution F
: with probability F(t), a message sent is received after delay t. Although the protocol dictates sending the vote after 4 seconds, there is a weak incentive to wait a little longer in case B is delayed for some reason and is received in time for B′ to build on it, albeit too late for attesters who voted at t=4 to have seen it.-}






import Engine.Engine
import Preprocessor.Preprocessor
import Examples.Auctions.AuctionSupportFunctions


import           Control.Monad.State  hiding (state,void)
import qualified Control.Monad.State  as ST
import           Data.List
import           Data.Tuple.Extra (uncurry3)

----------
-- A Model
----------

----------
-- 0 Types
----------
-- HashBlock choice
data Send = Send | DoNotSend
   deriving (Eq,Ord,Show)

-- A view on the previous information
data View a = HashBlock a | Empty
   deriving (Eq,Ord,Show)

type Started = Bool


------------------------
-- 1 Auxiliary functions
------------------------
-- given a string and the send decision, send a string
sendHash :: String -> String -> Send -> String
sendHash oldHash newHash DoNotSend = oldHash
sendHash oldHash newHash Send      = newHash


attestHash :: String -> View String -> String
attestHash mempty  _         = mempty
attestHash _       (HashBlock x)  = x
attestHash _       Empty     = mempty

-- Given a previousString and the timer, produce a newString at t=0 and keep the old one instead
createRandomString :: Int -> String -> Stochastic String
createRandomString 0 str = do
  r <- uniformDist ["abc","def","ghi"]
  pure (r ++ str)
createRandomString _ str = playDeterministically str


transformTicker :: Int -> Int
transformTicker 12 = 0
transformTicker x  = x + 1


attestedCorrect hashOld hashNew = isInfixOf hashOld hashNew


-- draw from a timer which determines whether the message is delayed
delaySendTime :: Int -> Int ->  Stochastic Int
delaySendTime actualTimer delayedTimer
  | actualTimer ==  0       = distFromList [(0,0.5),(5,0.5)]
  | delayedTimer == 5 = playDeterministically delayedTimer
  | otherwise         = playDeterministically actualTimer

-- given timers send old message or new message
delayMessage :: (Int, Int, String, String) -> String
delayMessage (actualTimer, delayedTimer, oldMessage, newMessage)
  | actualTimer < delayedTimer = oldMessage
  | otherwise                  = newMessage
------------
-- 2 Payoffs
------------

-- The attester is rewarded if their vote is included in block B′
-- and is correct, i.e., voted ∅ if B′ did not build on B, and hash(B)
-- otherwise.
attesterPayoff successFee verified = if verified then successFee else 0

proposerPayoff reward verified  = if verified then reward else 0

---------------------
-- 1 Game blocks

-- Generate hash given previous information
-- At time t=0 a new string is generated; otherwise the same old string is still used
hashGenerator = [opengame|

    inputs    : ticker, hash ;
    feedback  :   ;

    :-----:
    inputs    : ticker, hash ;
    feedback  :   ;
    operation : liftStochasticForward $ uncurry createRandomString ;
    outputs   : newString ;
    returns   : ;

    :-----:

    outputs   : newString ;
    returns   :           ;
  |]



-- A proposer observes the ticker and decides to send the block or not
-- If the decision is to send, the exogenous block is sent, otherwise the empty string
-- There is a delay built in, determined at t=0. If true, the new message is not sent but the old message is until the delay if over.
proposer  reward = [opengame|

    inputs    : ticker, delayedTicker, hashOld ;
    feedback  :   ;

    :-----:
    inputs    : ticker, hashOld ;
    feedback  :   ;
    operation : hashGenerator ;
    outputs   : proposedHash;
    returns   : ;
    // ^ creates new hash at t=0

    inputs    : ticker ;
    feedback  :   ;
    operation : dependentDecision "proposer" (const [Send,DoNotSend]) ;
    outputs   : sent ;
    returns   : 0;
    // ^ decision whether to send a message or not
    // ^ fix reward to zero; is update where it is evaluated as correct or false

    inputs    : hashOld, proposedHash, sent ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 sendHash ;
    outputs   : hashNew ;
    returns   : ;
    // ^ if the proposer decided to send the message, update the block, else keep the old block

    inputs    : ticker, delayedTicker ;
    feedback  :   ;
    operation : forwardFunction $ uncurry delaySendTime ;
    outputs   : delayedTickerUpdate ;
    returns   : ;
    // ^ determines whether message is delayed or not

    inputs    : ticker, delayedTicker, hashOld, hashNew ;
    feedback  :   ;
    operation : forwardFunction $ delayMessage ;
    outputs   : messageSent ;
    returns   : ;
    // ^ for a given timer, determines whether the block is sent or not

    :-----:

    outputs   : messageSent, delayedTickerUpdate ;
    returns   :  ;
  |]

-- The attester observes the sent hash, the old hash, the timer, and can then decide whether to send the latest hash or not
attester fee = [opengame|

    inputs    : ticker,hashNew,hashOld ;
    feedback  :  ;

    :-----:
    inputs    : ticker,hashNew,hashOld ;
    feedback  :   ;
    operation : dependentDecision "attester" (\(ticker, hashNew, hashOld) -> [hashNew,hashOld]) ;
    outputs   : attested ;
    returns   : 0 ;
    // ^ the attester either can send the newHash or the oldHash
    // ^ NOTE the payoff for the attester comes from the next period
    // ^ This needs to be carefully modelled
    // ^ Could make sense to make sense to model this in period
    :-----:

    outputs   : attested ;
    returns   :  ;
  |]

-- attesterPayoff fee correctAttestedNew ;
-- proposerPayoff reward correctSent ;

updatePayoffAttester fee  = [opengame|
    inputs    : bool ;
    feedback  :   ;

    :-----:
    inputs    : bool ;
    feedback  :   ;
    operation : forwardFunction $ attesterPayoff fee ;
    outputs   : value ;
    returns   : ;
    // ^ Determines the value


    inputs    : value ;
    feedback  :   ;
    operation : addPayoffs "attester" ;
    outputs   : ;
    returns   : ;
    // ^ Could make sense to make sense to model this in period
    :-----:

    outputs   :  ;
    returns   :  ;

  |]

updatePayoffProposer  reward  = [opengame|
    inputs    : bool ;
    feedback  :   ;

    :-----:
    inputs    : bool ;
    feedback  :   ;
    operation : forwardFunction $ proposerPayoff reward ;
    outputs   : value ;
    returns   : ;
    // ^ Determines the value


    inputs    : value ;
    feedback  :   ;
    operation : addPayoffs "proposer" ;
    outputs   : ;
    returns   : ;
    // ^ Could make sense to make sense to model this in period
    :-----:

    outputs   :  ;
    returns   :  ;

  |]



-------------------
-- 2 Complete games
-------------------

-- One round game
oneRound :: Double
         -> Double
         -> OpenGame
               StochasticStatefulOptic
               StochasticStatefulContext
               '[Kleisli Stochastic Int Send,
                 Kleisli Stochastic (Int, String, String) String]
               '[[DiagnosticInfoBayesian Int Send],
                 [DiagnosticInfoBayesian (Int, String, String) String]]
               (Int, Int, String, [Char])
               ()
               (String, [Char], Stochastic Int)
               ()
oneRound reward fee = [opengame|

    inputs    : ticker, delayedTicker, hashOld, attesterHash ;
    feedback  :   ;

    :-----:
    inputs    : ticker,delayedTicker,hashOld ;
    feedback  :   ;
    operation : proposer reward ;
    outputs   : hashNew, delayedTickerUpdate ;
    returns   : ;

    inputs    : ticker, hashNew, hashOld ;
    feedback  :   ;
    operation : attester fee ;
    outputs   : attested ;
    returns   : ;

    inputs    : attesterHash, hashNew ;
    feedback  :   ;
    operation : forwardFunction $ uncurry attestedCorrect ;
    outputs   : correctAttested ;
    returns   : ;
    // ^ This determines the payoff for the attester before
    // ^ Negative payoff for the attester, if the proposed hash has elements that where not reported by the attester before
    // ^ TODO this block needs to change, currently completely deterministic in the detection

    inputs    : correctAttested ;
    feedback  :   ;
    operation : updatePayoffAttester fee ;
    outputs   : ;
    returns   : ;
    // ^ Updates the payoff of the attester from the period before


    inputs    : attesterHash, hashNew ;
    feedback  :   ;
    operation : forwardFunction $ uncurry attestedCorrect ;
    outputs   : correctSent ;
    returns   : ;
    // ^ This determines the correctness for the proposer

    inputs    : correctSent ;
    feedback  :   ;
    operation : updatePayoffProposer reward;
    outputs   : ;
    returns   : ;
    // ^ Updates the payoff of the proposer from the period before



    :-----:

    outputs   : attested, hashNew, delayedTickerUpdate ;
    returns   :  ;
  |]

-- Repeated game
repeatedGame reward fee = [opengame|

    inputs    : ticker,delayedTicker, blockHash, attesterHash ;
    feedback  :   ;

    :-----:
    inputs    : ticker,delayedTicker, blockHash, attesterHash ;
    feedback  : correctAttestedOld  ;
    operation : oneRound reward fee ;
    outputs   : attested, hashNew, delayedTickerUpdate ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;


    :-----:

    outputs   : tickerNew, delayedTickerUpdate, attested, hashNew ;
    returns   :  ;
  |]


----------------
-- Continuations
-- extract continuation
-- extract continuation
extractContinuation :: StochasticStatefulOptic (Int, Int, String, [Char]) () (Int, Stochastic Int, String, [Char]) ()
                    -> (Int, Stochastic Int, String, [Char])
                    -> StateT Vector Stochastic ()
extractContinuation (StochasticStatefulOptic v u) (i, j, str1, str2) = do
  j' <- ST.lift j
  let x = (i, j', str1, str2)
  (z,a) <- ST.lift (v x)
  u z ()

-- extract next state (action)
extractNextState :: StochasticStatefulOptic (Int, Int, String, [Char]) () (Int, Stochastic Int, String, [Char]) ()
                 -> (Int, Stochastic Int, String, [Char])
                 -> Stochastic (Int, Stochastic Int, String, [Char])
extractNextState (StochasticStatefulOptic v _) (i, j, str1, str2) = do
  j' <- j
  let x = (i, j', str1, str2)
  (z,a) <- v x
  pure a

-- determine continuation for iterator, with the same repeated strategy
determineContinuationPayoffs 1        strat action = pure ()
determineContinuationPayoffs iterator strat action = do
   extractContinuation executeStrat action
   nextInput <- ST.lift $ extractNextState executeStrat action
   determineContinuationPayoffs (pred iterator) strat nextInput
 where executeStrat =  play (repeatedGame 2 2) strat


executeStrat strat =  play (repeatedGame 2 2) strat

-- fix context used for the evaluation
contextCont iterator strat initialAction = StochasticStatefulContext (pure ((),initialAction)) (\_ action -> determineContinuationPayoffs iterator strat action)


-----------
-- Analysis

--
strategyProposer :: Kleisli Stochastic Int Send
strategyProposer = pureAction Send

strategyAttester :: Kleisli Stochastic (Int, String, String) String
strategyAttester = Kleisli (\(_, newHash, _) -> pure newHash)

strategyTuple = strategyProposer ::- strategyAttester ::- Nil

strategyProposer' :: Kleisli Stochastic Int Send
strategyProposer' = pureAction DoNotSend

strategyAttester' :: Kleisli Stochastic (Int, String, String) String
strategyAttester' = Kleisli (\(_, newHash, _) -> pure "")


strategyTuple' = strategyProposer' ::- strategyAttester' ::- Nil


-- Start with the situation of one attester and one proposer
initialState = (0,0,"a","")

contextFixed =  StochasticStatefulContext (pure ((),initialState)) (\_ _ -> pure ())

eq iterator strat = generateIsEq $ evaluate (repeatedGame 2 2) strat (contextCont iterator strat initialState)

showOutput iterator strat = generateOutput $ evaluate (repeatedGame 2 2) strat (contextCont iterator strat initialState)
