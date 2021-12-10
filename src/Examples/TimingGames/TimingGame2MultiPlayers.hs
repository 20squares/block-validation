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

-- TODO Can we implement two games in parallel which get put together again?
-- TODO Implement the renumeration of the proposer for later periods
-- TODO Currently, the proposer is also not affected by not proposing something; only the attester suffers
-- DONE Check the initial state conditions make sense
-- DONE Test that the payoff version actually works
-- DONE Testing of equilibrium
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

NOTE: That seems to be a critical assumption. With two players, how can we actually confirm the state of the world? More generally, is the state of the world what the attesters decide? Or is there some additional source of truth?


Propagation times follow some distribution F
: with probability F(t), a message sent is received after delay t. Although the protocol dictates sending the vote after 4 seconds, there is a weak incentive to wait a little longer in case B is delayed for some reason and is received in time for B′ to build on it, albeit too late for attesters who voted at t=4 to have seen it.


# Multiplayer

The rules remain pretty much the same, but now we have multiple attesters at each round. We have a tree of blocks and we consider the head block to be the leaf that has accumulated the most attestations, according to the GHOST rule.

    GHOST rule: Start from the root and find the weight of each block by recursively going through each child and counting the number of votes downstream. The canonical chain starts from the root and at each fork chooses the block with the highest weight. The head of the chain is the first encountered leaf.

    Attesters from slot n

are expected to vote for the head of the chain at that slot. They may believe the head of the chain is h(n−1) if they don’t receive h(n) in time, but later on, if h(n) becomes part of the canonical chain, these attesters would be given 0

    .
    A weight-giving vote is a head vote from any attester.

## Proposed model

There are two stages, two block proposers and four attesters in total, two per block. A root block h(0)

is given.

    The first block proposer is expected to propose on the root block, h↑(1)=h(0)

.
a. If the first two attesters (A & B) see the block, they should vote on h(1), otherwise h(0)
.
The second proposer may propose either on h(0)
or h(1)

NOTE: Does this mean, the 2nd proposer sees the initial block? How can he otherwise choose?

    .
    b. The next two attesters (C & D) vote on the block they believe to be the head.

We either have:

a. a linear graph h(0)↓h(1)↓h(2)

, or

b. a fork (h(0)↓h(1))&(h(0)↓h(2))

.

In the case of a linear graph, if attesters A & B voted on h(1)
, they receive r. If C & D voted on h(2), they receive r. If either of the attesters didn’t vote on the correct block, they receive 0

(A and B could have different behaviours).

In the case of a fork, the head is either h(1)
or h(2). This is determined by the GHOST rule. For instance, if A votes h(0), C and D vote h(2), then h(2) will be the head, and A, C and D would be rewarded, while both proposer B(1) and attester B would get 0.

-}


-------------------------------------------------------------------------------------
-- Builds on TimingGame2
-- Multiplayer version of the game



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


-- Given a previousString and the timer, produce a newString at t=0 and keep the old one instead
createRandomString :: Int -> String -> Stochastic String
createRandomString 0 str = do
  r <- uniformDist ["abc","def","ghi"]
  pure (r ++ str)
createRandomString _ str = playDeterministically str


transformTicker :: Int -> Int
transformTicker 12 = 0
transformTicker x  = x + 1

-- Did the attester forward the correct state of the world?
attestedCorrect hashOld hashNew = isSuffixOf hashOld hashNew

-- Did the proposer send the block? Gets rewarded if one of the attesters says so
proposedCorrect hashOld hashNew1 hashNew2 = true1 && true2
  where true1 = isSuffixOf hashOld hashNew1
        true2 = isSuffixOf hashOld hashNew2

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
    // ^ fix reward to zero; it is later updated where it is evaluated as correct or false

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
attester name fee = [opengame|

    inputs    : ticker,hashNew,hashOld ;
    feedback  :  ;

    :-----:
    inputs    : ticker,hashNew,hashOld ;
    feedback  :   ;
    operation : dependentDecision name (\(ticker, hashNew, hashOld) -> [hashNew,hashOld]) ;
    outputs   : attested ;
    returns   : 0 ;
    // ^ the attester either can send the newHash or the oldHash
    // ^ NOTE the payoff for the attester comes from the next period
    // ^ This needs to be carefully modelled
    :-----:

    outputs   : attested ;
    returns   :  ;
  |]

-- attesterPayoff fee correctAttestedNew ;
-- proposerPayoff reward correctSent ;

updatePayoffAttester name fee  = [opengame|
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
    operation : addPayoffs name ;
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
               '[ Kleisli Stochastic Int Send
                , Kleisli Stochastic (Int, String, String) String
                , Kleisli Stochastic (Int, String, String) String]
               '[ [DiagnosticInfoBayesian Int Send]
                , [DiagnosticInfoBayesian (Int, String, String) String]
                , [DiagnosticInfoBayesian (Int, String, String) String]]
               (Int, Int, String, [Char], [Char])
               ()
               (String, String, [Char], Stochastic Int)
               ()
oneRound  reward fee = [opengame|

    inputs    : ticker, delayedTicker, hashOld, attesterHash1, attesterHash2 ;
    feedback  :   ;

    :-----:
    inputs    : ticker,delayedTicker,hashOld ;
    feedback  :   ;
    operation : proposer reward ;
    outputs   : hashNew, delayedTickerUpdate ;
    returns   : ;
    // ^ Proposer makes a decision

    inputs    : ticker, hashNew, hashOld ;
    feedback  :   ;
    operation : attester "attester1" fee ;
    outputs   : attested1 ;
    returns   : ;
    // ^ Attester1 makes a decision

    inputs    : ticker, hashNew, hashOld ;
    feedback  :   ;
    operation : attester "attester2" fee ;
    outputs   : attested2 ;
    returns   : ;
    // ^ Attester2 makes a decision

    inputs    : attesterHash1, hashNew ;
    feedback  :   ;
    operation : forwardFunction $ uncurry attestedCorrect ;
    outputs   : correctAttested1 ;
    returns   : ;
    // ^ This determines whether attester 1 was correct in period (t-1)

    inputs    : attesterHash2, hashNew ;
    feedback  :   ;
    operation : forwardFunction $ uncurry attestedCorrect ;
    outputs   : correctAttested2 ;
    returns   : ;
    // ^ This determines whether attester 2 was correct in period (t-1)


    inputs    : correctAttested1 ;
    feedback  :   ;
    operation : updatePayoffAttester "attester1" fee ;
    outputs   : ;
    returns   : ;
    // ^ Updates the payoff of attester 1 given decision in period (t-1)

    inputs    : correctAttested2 ;
    feedback  :   ;
    operation : updatePayoffAttester "attester2" fee ;
    outputs   : ;
    returns   : ;
    // ^ Updates the payoff of attester 2 given decision in period (t-1)

    inputs    : attesterHash1, attesterHash2, hashNew ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 proposedCorrect ;
    outputs   : correctSent ;
    returns   : ;
    // ^ This determines whether the proposer was correct in period (t-1)



    inputs    : correctSent ;
    feedback  :   ;
    operation : updatePayoffProposer reward;
    outputs   : ;
    returns   : ;
    // ^ Updates the payoff of the proposer given decision in period (t-1)

    :-----:

    outputs   : attested1, attested2, hashNew, delayedTickerUpdate ;
    returns   :  ;
  |]

-- Repeated game
repeatedGame reward fee = [opengame|

    inputs    : ticker,delayedTicker, blockHash, attesterHash1, attesterHash2 ;
    feedback  :   ;

    :-----:
    inputs    : ticker,delayedTicker, blockHash, attesterHash1, attesterHash2 ;
    feedback  : correctAttestedOld  ;
    operation : oneRound reward fee ;
    outputs   : attested1, attested2, hashNew, delayedTickerUpdate ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;


    :-----:

    outputs   : tickerNew, delayedTickerUpdate, attested1, attested2, hashNew ;
    returns   :  ;
  |]


----------------
-- Continuations
-- extract continuation
-- extract continuation
extractContinuation :: StochasticStatefulOptic (Int, Int, String, [Char], [Char]) () (Int, Stochastic Int, String, [Char], [Char]) ()
                    -> (Int, Stochastic Int, String, [Char], [Char])
                    -> StateT Vector Stochastic ()
extractContinuation (StochasticStatefulOptic v u) (i, j, str1, str2, str3) = do
  j' <- ST.lift j
  let x = (i, j', str1, str2, str3)
  (z,a) <- ST.lift (v x)
  u z ()

-- extract next state (action)
extractNextState :: StochasticStatefulOptic (Int, Int, String, [Char], [Char]) () (Int, Stochastic Int, String, [Char], [Char]) ()
                 -> (Int, Stochastic Int, String, [Char], [Char])
                 -> Stochastic (Int, Stochastic Int, String, [Char], [Char])
extractNextState (StochasticStatefulOptic v _) (i, j, str1, str2, str3) = do
  j' <- j
  let x = (i, j', str1, str2, str3)
  (z,a) <- v x
  pure a

-- determine continuation for iterator, with the same repeated strategy
determineContinuationPayoffs 1        strat action = pure ()
determineContinuationPayoffs iterator strat action = do
   extractContinuation executeStrat action
   nextInput <- ST.lift $ extractNextState executeStrat action
   determineContinuationPayoffs (pred iterator) strat nextInput
 where executeStrat =  play (repeatedGame  2 2) strat


executeStrat strat =  play (repeatedGame 2 2) strat

-- fix context used for the evaluation
contextCont iterator strat initialAction = StochasticStatefulContext (pure ((),initialAction)) (\_ action -> determineContinuationPayoffs iterator strat action)


-----------
-- Analysis

--
strategyProposer :: Kleisli Stochastic Int Send
strategyProposer = pureAction Send

strategyProposer' :: Kleisli Stochastic Int Send
strategyProposer' = pureAction DoNotSend

strategyAttester :: Kleisli Stochastic (Int, String, String) String
strategyAttester = Kleisli (\(_, newHash, _) -> pure newHash)

strategyAttester' :: Kleisli Stochastic (Int, String, String) String
strategyAttester' = Kleisli (\(_, _, oldHash) -> pure oldHash)

strategyAttester'' :: Kleisli Stochastic (Int, String, String) String
strategyAttester'' = Kleisli (\(_, newHash, oldHash) -> uniformDist [newHash,oldHash])



strategyTuple = strategyProposer ::- strategyAttester ::- Nil

strategyTuple2 = strategyProposer' ::- strategyAttester' ::- Nil

strategyTuple3 = strategyProposer' ::- strategyAttester ::- Nil

strategyTuple4 = strategyProposer ::- strategyAttester' ::- Nil

strategyTuple5 = strategyProposer' ::- strategyAttester'' ::- Nil

strategyTuple6 = strategyProposer ::- strategyAttester'' ::- Nil
-- Start with the situation of one attester and one proposer
initialState = (0,0,"a","")

contextFixed =  StochasticStatefulContext (pure ((),initialState)) (\_ _ -> pure ())

eq iterator strat initialState = generateIsEq $ evaluate (repeatedGame  2 2) strat (contextCont iterator strat initialState)

showOutput iterator strat initialState = generateOutput $ evaluate (repeatedGame  2 2) strat (contextCont iterator strat initialState)

-------------------
-- Scenarios Tested

{-
-- NOTE Both players truthtelling is also an equilibrium
eq 2 strategyTuple (1,0,"a","")
eq 2 strategyTuple (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple (1,0,"a","a")
eq 2 strategyTuple (0,0,"a","a")


-- NOTE this is a scenario where both players coordinate against the true value; but the strategy of the attester is irrelevant here as he only sees the same information
eq 2 strategyTuple2 (1,0,"a","")
eq 2 strategyTuple2 (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple2 (1,0,"a","a")
eq 2 strategyTuple2 (0,0,"a","a")

-- NOTE proposer not telling the truth but attester is, is also an equilibrium. Makes sense as the attester can only attest what is there
eq 2 strategyTuple3 (1,0,"a","")
eq 2 strategyTuple3 (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple3 (1,0,"a","a")
eq 2 strategyTuple3 (0,0,"a","a")

-- NOTE proposer telling the truth but attester is not, is _not_ an equilibrium.
eq 2 strategyTuple4 (0,0,"a","")
-- Also is an equilibrium if the initial values are the same
eq 2 strategyTuple4 (0,0,"a","a")

-- NOTE the behavior above depends on the state!
eq 2 strategyTuple4 (1,0,"a","")
eq 2 strategyTuple4 (1,0,"a","a")
-}
