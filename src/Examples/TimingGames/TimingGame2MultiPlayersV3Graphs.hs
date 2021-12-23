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

module Examples.TimingGames.TimingGame2MultiPlayersV3Graphs where

-- TODO Simplify find vertex by id, comes up at several points
-- TODO Test graph functions
-- TODO Extend it towards another proposer game following the initial one
-- TODO Should we simplify the building on previous blocks?
-- TODO Implement the sequence; how can we collect votes on the game tree? Make the graph an internal state of the game and update it accordingly at each step?
-- TODO Implement a hard-coded two stage version as well
-- DONE In the case of a fork, the head is either h(1) or h(2). This is determined by the GHOST rule. For instance, if A votes h(0), C and D vote h(2), then h(2) will be the head, and A, C and D would be rewarded, while both proposer B(1) and attester B would get 0.
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

import           Algebra.Graph.Relation
import           Control.Monad.State  hiding (state,void)
import qualified Control.Monad.State  as ST
import           Data.List
import qualified Data.Map.Strict      as M
import qualified Data.Set             as S
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

type Hash = Word
type Player = String
type Vote = Int
type Id    = Int
type Timer = Int

-- The chain is represented by the edges (Blocks) and vertices (Which attester voted for that Block to be the head)
type Chain = Relation (Id,Vote)

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


-- Given a previous chain, id, and a new hash, extend the chain accordingly
-- initially, that vertex has empty votes
-- it is assigned a unique id
addToChain :: Chain -> Id -> Chain
addToChain chain id  =
  let newId = vertexCount chain + 1
      -- ^ assign new id using the vertexCount of the existing chain
      newNode = vertex (newId,0)
      -- ^ create new vertex with 0 votes
      vertexRoot = induce (\(x,_) -> x == id) chain
      -- ^ find vertex with the _id_
      newConnection = connect vertexRoot newNode
      -- ^ connect the vertex with the relevant id to new node with label new hash
      in overlay chain newConnection
      -- ^ update the connection of the new chain

-- Find vertex in a chain given unique id
findVertexById :: Chain -> Id -> (Id,Vote)
findVertexById chain id =
  let  verticeLs = vertexList chain
       -- ^ list of vertices
       in head $ filter (\(id',_) -> id' == id) verticeLs

-- For attester choose the string which he believes is the head and update the chain accordingly
attesterChoiceIndex :: Chain -> Id -> Chain
attesterChoiceIndex chain id =
  let (id',i) = findVertexById chain id
      in replaceVertex (id',i) (id',i+1) chain

-- Given an initial chain and a list of votes on _Id_s, update the chain
updateVotes :: Chain -> [Id] -> Chain
updateVotes chain [] = chain
updateVotes chain (i:is) = updateVotes (attesterChoiceIndex chain i) is

-- Cycling ticker
transformTicker :: Timer -> Timer
transformTicker 12 = 0
transformTicker x  = x + 1

-- Did the attester forward the correct state of the world?
-- Compare the hash he reported (in t-1) with current block
-- Is the tail the same?
attestedCorrect2 name hashMap hashNew =
  let hashOld = hashMap M.! name
     in hashOld == (tail hashNew)

-- Is the node the attester voted for on the path to the latest head?
attestedCorrect :: Player -> M.Map Player Id -> Chain -> Id -> Bool
attestedCorrect name map chain headOfChain =
  let idChosen = map M.! name
      -- ^ id voted for by player
      chosenNode = findVertexById chain idChosen
      -- ^ vertex chosen
      headNode = findVertexById chain headOfChain
      -- ^ vertex which is head of the chain
      chainClosure = closure chain
      -- ^ transitive closure of chain
      setOnPath = postSet chosenNode chainClosure
      -- ^ elements that are successors of id'
      in S.member headNode setOnPath
      -- ^ is the head in that successor set?

-- Find the current head of a chain according to GHOST
determineHead :: Chain -> Id
determineHead chain =
  let root = findRoot chain
      in fst $ findHead chain root
  where
      -- Finds the root for a chain
      findRoot :: Chain -> (Id,Vote)
      findRoot chain =
        let adjLs = adjacencyList chain
            ls    = vertexList chain
            -- FIXME head
            in head $ findRoots ls adjLs
        where
          findRoots :: Eq a => [a] -> [(a,[a])] -> [a]
          findRoots [] ls     = []
          findRoots (x:xs) ls =
            if null $ filter (\(y,ys) -> elem x ys) ls
              then x : findRoots xs ls
              else findRoots xs ls
      -- Given a chain and a starting node, finds the head with the most weights along the path
      -- FIXME
      findHead :: Chain -> (Id,Vote) -> (Id,Vote)
      findHead chain root =
        if S.null nextVertexSet
            then root
            else let (vote,id) = S.findMax $ S.map (\(x,y) -> (y,x)) nextVertexSet
                    in findHead chain (id,vote)
        where nextVertexSet = postSet root chain

-- Did the proposer from (t-1) send the block? Gets rewarded if that block is on the path to the current head.
proposedCorrect :: Chain -> Id -> Bool
proposedCorrect chain headOfChain =
  let pastHeadId  = vertexCount chain - 1
      pastHead    = findVertexById chain pastHeadId
      currentHead = findVertexById chain headOfChain
      onPathElems = postSet currentHead chain
      in S.member pastHead onPathElems


-- draw from a timer which determines whether the message is delayed
delaySendTime :: Int -> Int ->  Stochastic Int
delaySendTime actualTimer delayedTimer
  | actualTimer ==  0       = distFromList [(0,0.5),(5,0.5)]
  | delayedTimer == 5 = playDeterministically delayedTimer
  | otherwise         = playDeterministically actualTimer

-- given timers send old message or new message
delayMessage :: (Timer, Timer, Chain, Chain) -> Chain
delayMessage (actualTimer, delayedTimer, oldChain, newChain)
  | actualTimer < delayedTimer = oldChain
  | otherwise                  = newChain

-- transform list to Map; done here due to restrictions of DSL
fromListToMap :: [(Player,Id)] -> M.Map Player Id
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
addBlock = [opengame|

    inputs    : chainOld, chosenId ;
    feedback  :   ;

    :-----:
    inputs    : chainOld, chosenId ;
    feedback  :   ;
    operation : forwardFunction $ uncurry addToChain ;
    outputs   : chainNew ;
    returns   : ;

    :-----:

    outputs   : chainNew ;
    returns   :          ;
  |]

-- A proposer observes the ticker and decides to send the block or not
-- If the decision is to send, the exogenous block is sent, otherwise the empty string
-- There is a delay built in, determined at t=0. If true, the new message is not sent but the old message is until the delay if over.
proposer  = [opengame|

    inputs    : ticker, delayedTicker, chainOld;
    feedback  :   ;

    :-----:
    inputs    : ticker, chainOld ;
    feedback  :   ;
    operation : dependentDecision "proposer" (\(t,chainOld) -> [0,vertexCount chainOld]) ;
    outputs   : sent ;
    returns   : 0;
    // ^ decision which hash to send forward (latest element, or second latest element etc.)
    // ^ NOTE fix reward to zero; it is later updated where it is evaluated as correct or false

    inputs    : chainOld, sent ;
    feedback  :   ;
    operation : addBlock ;
    outputs   : chainNew;
    returns   : ;
    // ^ creates new hash at t=0


    inputs    : ticker, delayedTicker ;
    feedback  :   ;
    operation : forwardFunction $ uncurry delaySendTime ;
    outputs   : delayedTickerUpdate ;
    returns   : ;
    // ^ determines whether message is delayed or not

    inputs    : ticker, delayedTicker, chainOld, chainNew ;
    feedback  :   ;
    operation : forwardFunction $ delayMessage ;
    outputs   : messageSent ;
    returns   : ;
    // ^ for a given timer, determines whether the block is sent or not

    :-----:

    outputs   : messageSent, delayedTickerUpdate ;
    returns   :  ;
  |]

-- The attester observes the sent hash, the old hash, the timer, and can then decide which node to attest as the head
attester name = [opengame|

    inputs    : ticker,chainNew,chainOld ;
    feedback  :  ;

    :-----:
    inputs    : ticker,chainNew,chainOld ;
    feedback  :   ;
    operation : dependentDecision name (\(ticker, chainNew, chainOld) -> [0, vertexCount chainNew]) ;
    outputs   : attestedIndex ;
    returns   : 0 ;
    // ^ the attester either can send the newHash or the oldHash
    // ^ NOTE the payoff for the attester comes from the next period

    :-----:

    outputs   : attestedIndex ;
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

determineHeadOfChain = [opengame|
    inputs    : chain ;
    feedback  :   ;

    :-----:
    inputs    : chain ;
    feedback  :   ;
    operation : forwardFunction $ determineHead ;
    outputs   : head ;
    returns   : ;
    // ^ Determines the head of the chain

    :-----:

    outputs   :  ;
    returns   :  ;

  |]


proposerPayment  reward = [opengame|

    inputs    : chainNew, headOfChain ;
    feedback  :   ;

    :-----:
    inputs    : chainNew, headOfChain ;
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

    outputs   : ;
    returns   :  ;
  |]



----------------------
-- 2 Group Game blocks

-- Group all attesters together
attestersGroupDecision :: OpenGame
                            StochasticStatefulOptic
                            StochasticStatefulContext
                            ('[Kleisli Stochastic (Timer, Relation (Id, Vote), Chain) Int,
                                Kleisli Stochastic (Timer, Relation (Id, Vote), Chain) Int])
                            ('[[DiagnosticInfoBayesian (Timer, Relation (Id, Vote), Chain) Int],
                                [DiagnosticInfoBayesian (Timer, Relation (Id, Vote), Chain) Int]])
                            (Timer, Relation (Id, Vote), Chain)
                            ()
                            (M.Map Player Id, Chain)
                            ()
attestersGroupDecision  = [opengame|

    inputs    : ticker,chainNew,chainOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker, chainNew, chainOld ;
    feedback  :   ;
    operation : attester "attester1"  ;
    outputs   : attested1 ;
    returns   : ;
    // ^ Attester1 makes a decision

    inputs    : ticker, chainNew, chainOld ;
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
    // ^ Creates a map of which attester voted for which index

    inputs    : chainNew, [attested1,attested2] ;
    feedback  : ;
    operation : forwardFunction $ uncurry updateVotes ;
    outputs   : chainNewUpdated;
    returns   : ;
    // ^ Updates the chain with the relevant votes


    :-----:

    outputs   : attesterHashMap, chainNewUpdated;
    returns   :  ;
  |]

-- Group payments by attesters
attestersPayment fee = [opengame|

    inputs    : attesterHashMap, chainNew, headId;
    feedback  :   ;

    :-----:
    inputs    : attesterHashMap, chainNew, headId ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 $ attestedCorrect "attester1" ;
    outputs   : correctAttested1 ;
    returns   : ;
    // ^ This determines whether attester 1 was correct in period (t-1) using the latest hash and the old information

    inputs    : attesterHashMap, chainNew, headId ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 $ attestedCorrect "attester2" ;
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

{--
-------------------
-- 2 Complete games
-------------------

-- One round game
oneRound  reward fee = [opengame|

    inputs    : ticker, delayedTicker, chainOld, attesterHashMapOld  ;
    // ^ chainOld is the old hash
    feedback  :   ;

    :-----:
    inputs    : ticker,delayedTicker,chainOld ;
    feedback  :   ;
    operation : proposer ;
    outputs   : chainNew, delayedTickerUpdate ;
    returns   : ;
    // ^ Proposer makes a decision, a new hash is proposed

    inputs    : ticker,chainNew,chainOld ;
    feedback  :   ;
    operation : attestersGroupDecision ;
    outputs   : attesterHashMapNew, chainNewUpdated ;
    returns   :  ;
    // ^ Attesters make a decision

    inputs    : attesterHashMapOld, chainNew, headNode ;
    feedback  :   ;
    operation : attestersPayment fee ;
    outputs   : ;
    returns   : ;
    // ^ Attesters get rewarded

    inputs    : chainOld, chainNew ;
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

    outputs   : attesterHashMapNew, chainNew, delayedTickerUpdate ;
    returns   :  ;
  |]

-- Repeated game
repeatedGame reward fee = [opengame|

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRound reward fee ;
    outputs   : attesterHashMapNew, chainNew, delayedTickerUpdate ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    :-----:

    outputs   : tickerNew, delayedTickerUpdate, attesterHashMapNew, chainNew ;
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
-}
