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

module Examples.TimingGames.TimingGame2MultiPlayersV2 where


-- TODO In the case of a fork, the head is either h(1) or h(2). This is determined by the GHOST rule. For instance, if A votes h(0), C and D vote h(2), then h(2) will be the head, and A, C and D would be rewarded, while both proposer B(1) and attester B would get 0.
-- TODO Extend it towards another proposer game following the initial one
-- TODO Should we simplify the building on previous blocks?
-- TODO Implement the sequence; how can we collect votes on the game tree? Make the graph an internal state of the game and update it accordingly at each step?
-- TODO Implement a hard-coded two stage version as well
-- DONE Implement the renumeration of the proposer for later periods - now that is clear how it works in principle
-- DONE Check payoffs for attesters
-- DONE Currently, the proposer is also not affected by not proposing something; only the attester suffers
-- DONE Check the initial state conditions make sense
-- DONE Test that the payoff version actually works
-- DONE Testing of equilibrium
-- DONE Can we remodel this game as to use the state hack as well?
-- DONE Do we need more attesters to make that model relevant?
-- DONE What is the payoff for the sender?
-- DONE Check strategies and explore game

-- FIXME For how long will the renumeration of attesters and proposer continue? Is it just for one period? Periods t?

-- NOTE Difference to version 1 is that the attester is deciding actively what the head of the game is

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
import qualified Data.Map.Strict      as M
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

-- Given the timer, produce a newString at t=0 and keep the old one instead
createRandomString :: Int -> Stochastic String
createRandomString 0 = uniformDist ["a","b"]
createRandomString _ = playDeterministically mempty


-- Given a previousString and the timer, produce a newString
addString :: String -> Int -> String -> String
addString str index new = new ++ drop index str

-- For attester choose the string which he believes is the head
attesterChoiceIndex :: String -> Int -> String
attesterChoiceIndex str index = drop index str

-- Cycling ticker
transformTicker :: Int -> Int
transformTicker 12 = 0
transformTicker x  = x + 1

-- Did the attester forward the correct state of the world?
-- Compare the hash he reported (in t-1) with current block
-- Is the tail the same?
attestedCorrect name hashMap hashNew =
  let hashOld = hashMap M.! name
     in hashOld == (tail hashNew)

-- Did the proposer send the block? Gets rewarded if the new proposed block builds on top of the old block
proposedCorrect hashOld hashNew = isSuffixOf hashOld hashNew

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

-- transform list to Map; done here due to restrictions of DSL
fromListToMap :: Ord a => [(a,b)] -> M.Map a b
fromListToMap = M.fromList
------------
-- 2 Payoffs
------------

  -- The attester  and the proposer are rewarded if their decision has been evaluated by _attestedCorrect_ resp. _proposedCorrect_ as correct
attesterPayoff successFee verified = if verified then successFee else 0
proposerPayoff reward verified  = if verified then reward else 0

---------------------
-- 1 Game blocks

-- Generate hash given previous information
-- At time t=0 a new string is generated; otherwise the same old string is still used
addHash = [opengame|

    inputs    : listHashes, sent, newProposedBlock  ;
    feedback  :   ;

    :-----:
    inputs    : listHashes, sent, newProposedBlock ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 addString ;
    outputs   : newListHashes ;
    returns   : ;

    :-----:

    outputs   : newListHashes ;
    returns   :               ;
  |]



-- A proposer observes the ticker and decides to send the block or not
-- If the decision is to send, the exogenous block is sent, otherwise the empty string
-- There is a delay built in, determined at t=0. If true, the new message is not sent but the old message is until the delay if over.
proposer  = [opengame|

    inputs    : ticker, delayedTicker, listHashes, newProposedBlock;
    feedback  :   ;

    :-----:
    inputs    : ticker, listHashes ;
    feedback  :   ;
    operation : dependentDecision "proposer" (\(t,listHashes) -> [0,length listHashes]) ;
    outputs   : sent ;
    returns   : 0;
    // ^ decision which hash to send forward (latest element, or second latest element etc.)
    // ^ NOTE fix reward to zero; it is later updated where it is evaluated as correct or false

    inputs    : listHashes, sent, newProposedBlock ;
    feedback  :   ;
    operation : addHash ;
    outputs   : proposedHash;
    returns   : ;
    // ^ creates new hash at t=0


    inputs    : ticker, delayedTicker ;
    feedback  :   ;
    operation : forwardFunction $ uncurry delaySendTime ;
    outputs   : delayedTickerUpdate ;
    returns   : ;
    // ^ determines whether message is delayed or not

    inputs    : ticker, delayedTicker, listHashes, proposedHash ;
    feedback  :   ;
    operation : forwardFunction $ delayMessage ;
    outputs   : messageSent ;
    returns   : ;
    // ^ for a given timer, determines whether the block is sent or not

    :-----:

    outputs   : messageSent, delayedTickerUpdate ;
    returns   :  ;
  |]

-- The attester observes the sent hash, the old hash, the timer, and can then decide which has to attest as the head
attester name = [opengame|

    inputs    : ticker,hashNew,hashOld ;
    feedback  :  ;

    :-----:
    inputs    : ticker,hashNew,hashOld ;
    feedback  :   ;
    operation : dependentDecision name (\(ticker, hashNew, hashOld) -> [0, length hashNew]) ;
    outputs   : attestedIndex ;
    returns   : 0 ;
    // ^ the attester either can send the newHash or the oldHash
    // ^ NOTE the payoff for the attester comes from the next period

    inputs    : hashNew, attestedIndex ;
    feedback  :   ;
    operation : forwardFunction $ uncurry attesterChoiceIndex ;
    outputs   : attestedHash;
    returns   : ;
    // ^ produces the new hash given the decision by the attester what constitutes the head

    :-----:

    outputs   : attestedHash ;
    returns   :  ;
  |]

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


----------------------
-- 2 Group Game blocks

-- Group all attesters together
attestersGroupDecision  = [opengame|

    inputs    : ticker,hashNew,listHashes ;
    feedback  :   ;

    :-----:

    inputs    : ticker, hashNew, listHashes ;
    feedback  :   ;
    operation : attester "attester1"  ;
    outputs   : attested1 ;
    returns   : ;
    // ^ Attester1 makes a decision

    inputs    : ticker, hashNew, listHashes ;
    feedback  :   ;
    operation : attester "attester2"  ;
    outputs   : attested2 ;
    returns   : ;
    // ^ Attester2 makes a decision

    inputs    : [("attester1",attested1),("attester2",attested2)] ;
    feedback  : ;
    operation : forwardFunction fromListToMap ;
    outputs   : attesterHashMap ;
    returns   : ;

    :-----:

    outputs   : attesterHashMap ;
    returns   :  ;
  |]

-- Group payments by attesters
attestersPayment fee = [opengame|

    inputs    : attesterHashMap, hashNew ;
    feedback  :   ;

    :-----:
    inputs    : attesterHashMap, hashNew ;
    feedback  :   ;
    operation : forwardFunction $ uncurry $ attestedCorrect "attester1" ;
    outputs   : correctAttested1 ;
    returns   : ;
    // ^ This determines whether attester 1 was correct in period (t-1) using the latest hash and the old information

    inputs    : attesterHashMap, hashNew ;
    feedback  :   ;
    operation : forwardFunction $ uncurry $ attestedCorrect "attester2" ;
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

        :-----:

    outputs   :  ;
    returns   :  ;
  |]


-------------------
-- 2 Complete games
-------------------

-- One round game
oneRound  reward fee = [opengame|

    inputs    : ticker, delayedTicker, proposerHashOld, attesterHashMapOld, newProposedBlock ;
    // ^ proposerHashOld is the old hash
    feedback  :   ;

    :-----:
    inputs    : ticker,delayedTicker,proposerHashOld,newProposedBlock ;
    feedback  :   ;
    operation : proposer ;
    outputs   : proposerHashNew, delayedTickerUpdate ;
    returns   : ;
    // ^ Proposer makes a decision, a new hash is proposed

    inputs    : ticker,proposerHashNew,proposerHashOld ;
    feedback  :   ;
    operation : attestersGroupDecision ;
    outputs   : attesterHashMapNew ;
    returns   :  ;
    // ^ Attesters make a decision

    inputs    : attesterHashMapOld, proposerHashNew ;
    feedback  :   ;
    operation : attestersPayment fee ;
    outputs   : ;
    returns   : ;
    // ^ Attesters get rewarded

    inputs    : proposerHashOld, proposerHashNew ;
    feedback  :   ;
    operation : forwardFunction $ uncurry proposedCorrect ;
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

    outputs   : attesterHashMapNew, proposerHashNew, delayedTickerUpdate ;
    returns   :  ;
  |]

-- Repeated game
repeatedGame reward fee = [opengame|

    inputs    : ticker,delayedTicker, attesterHashMapOld, proposerHashOld ;
    feedback  :   ;

    :-----:
    inputs    : ticker ;
    feedback  :   ;
    operation : liftStochasticForward $ createRandomString ;
    outputs   : newProposedBlock ;
    returns   : ;


    inputs    : ticker,delayedTicker, proposerHashOld, attesterHashMapOld, newProposedBlock ;
    feedback  :   ;
    operation : oneRound reward fee ;
    outputs   : attesterHashMapNew, listHashesNew, delayedTickerUpdate ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    :-----:

    outputs   : tickerNew, delayedTickerUpdate, attesterHashMapNew, listHashesNew ;
    returns   :  ;
  |]

----------------
-- Continuations
-- extract continuation
-- extract continuation
extractContinuation :: StochasticStatefulOptic (Int, Int, M.Map String String, String) () (Int, Stochastic Int, M.Map String String, String) ()
                    -> (Int, Stochastic Int, M.Map String String, String)
                    -> StateT Vector Stochastic ()
extractContinuation (StochasticStatefulOptic v u) (i, j, strMap, str) = do
  j' <- ST.lift j
  let x = (i, j', strMap, str)
  (z,a) <- ST.lift (v x)
  u z ()

-- extract next state (action)
extractNextState :: StochasticStatefulOptic (Int, Int, M.Map String String, String) () (Int, Stochastic Int, M.Map String String, String) ()
                 -> (Int, Stochastic Int, M.Map String String, String)
                 -> Stochastic (Int, Stochastic Int, M.Map String String, String)
extractNextState (StochasticStatefulOptic v _) (i, j, strMap, str) = do
  j' <- j
  let x = (i, j', strMap, str)
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
