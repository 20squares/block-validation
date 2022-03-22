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

module Examples.TimingGames.GraphGames.InternalDebug where

import           Engine.Engine
import           Preprocessor.Preprocessor

import           Algebra.Graph.Relation
import           Control.Monad.State  hiding (state,void)
import qualified Control.Monad.State  as ST
import qualified Data.Map.Strict      as M
import           Data.NumInstances.Tuple
-- NOTE ^^ this is for satisfying the class restrictions of Algebra.Graph.Relation
import qualified Data.Set             as S
import           Data.Tuple.Extra (uncurry3)


-----------------------------------
-- Same as `Internal.hs`
-- But contains some dummy players
-- for debugging reasons

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
type Weight = Int
type AttesterMap = M.Map Player Id
-- The chain is represented by the edges (Blocks) and vertices (Which attester voted for that Block to be the head)
type Chain = Relation (Id,Vote)
type WeightedChain = Relation (Id,Weight)

------------------------
-- 1 Auxiliary functions
------------------------

-- Given a previous chain, id, and a new hash, extend the chain accordingly
-- initially, that vertex has empty votes
-- it is assigned a unique id
-- FIXME What if non existing id?
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
-- FIXME What if non-existing id?
findVertexById :: Chain -> Id -> (Id,Vote)
findVertexById chain id =
  let  verticeLs = vertexList chain
       -- ^ list of vertices
       in (head $ filter (\(id',_) -> id' == id) verticeLs)

-- For attester choose the string which he believes is the head and update the chain accordingly
-- FIXME What if non-existing id?
attesterChoiceIndex :: Chain -> Id -> Chain
attesterChoiceIndex chain id =
  let (id',i) = findVertexById chain id
      in replaceVertex (id',i) (id',i+1) chain

-- Given an initial chain and a list of votes on _Id_s, update the chain
-- FIXME What if non-existing id?
updateVotes :: Chain -> [Id] -> Chain
updateVotes chain [] = chain
updateVotes chain (i:is) = updateVotes (attesterChoiceIndex chain i) is

-- Cycling ticker
transformTicker :: Timer -> Timer
transformTicker 12 = 0
transformTicker x  = x + 1


-- find the head of the chain
determineHead :: Chain -> Id
determineHead chain =
  let allBranches = findBranches chain
      weightedBranches = S.map (findPath chain) allBranches
      (weightMax,idMax) = S.findMax $ S.map (\(x,y) -> (y,x)) weightedBranches
      in idMax
  where
    -- find all the branches of a chain
    findBranches :: Chain  -> S.Set (Id,Vote)
    findBranches chain' =
      let  vertexSetChain   = vertexSet chain'
           transChain = transitiveClosure chain'
           setPreSet = S.unions $ S.map (flip preSet transChain) vertexSetChain
           in S.difference vertexSetChain setPreSet
    -- find all the paths from each branch to the root of the chain
    findPath :: Chain -> (Id, Vote) -> (Id, Weight)
    findPath chain' (i,v) =
      let elementsOnPath = preSet (i,v) transitiveChain
          transitiveChain = transitiveClosure chain'
          weight = S.foldr (\(_,j) -> (+) j) 0 elementsOnPath
          in (i,weight + v)
          -- ^ NOTE the value of the last node itself is added as well

-- Is the node the attester voted for on the path to the latest head?
-- FIXME player name, id not given
attestedCorrect :: Player -> M.Map Player Id -> Chain -> Id -> Bool
attestedCorrect name map chain headOfChain =
  let idChosen = map M.! name
      -- ^ id voted for by player
      chosenNode = findVertexById chain idChosen
      -- ^ vertex chosen
      headNode = findVertexById chain headOfChain
      -- ^ vertex which is head of the chain
      chainClosure = closure chain
      -- ^ transitive closure of chain; needed to get all connections
      setOnPath = postSet chosenNode chainClosure
      -- ^ elements that are successors of id'
      in S.member headNode setOnPath
      -- ^ is the head in that successor set?

-- Did the proposer from (t-1) send the block? Gets rewarded if that block is on the path to the current head.
proposedCorrect :: Chain -> Bool
proposedCorrect chain  =
  let currentHeadId = determineHead chain
      currentHead   = findVertexById chain currentHeadId
      oldDecisionProposer = vertexCount chain - 1
      chainClosure  = closure chain
      onPathElems   = preSet currentHead chainClosure
      pastHead      = findVertexById chain oldDecisionProposer
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
newAttesterMap :: [(Player,Id)] -> AttesterMap -> AttesterMap
newAttesterMap new old = M.union (M.fromList new) old

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
proposer  name = [opengame|

    inputs    : ticker, delayedTicker, chainOld;
    feedback  :   ;

    :-----:
    inputs    : ticker, chainOld ;
    feedback  :   ;
    operation : dependentDecision name (\(t,chainOld) -> [1,vertexCount chainOld]) ;
    outputs   : decisionProposer ;
    returns   : 0;
    // ^ decision which hash to send forward (latest element, or second latest element etc.)
    // ^ NOTE fix reward to zero; it is later updated where it is evaluated as correct or false

    inputs    : chainOld, decisionProposer ;
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
    outputs   : messageChain ;
    returns   : ;
    // ^ for a given timer, determines whether the block is decisionProposer or not

    :-----:

    outputs   : messageChain, delayedTickerUpdate ;
    // ^ newchain (if timer allows otherwise old chain), update on delayedticker, decisionProposer
    returns   :  ;
  |]

-- The attester observes the sent hash, the old hash, the timer, and can then decide which node to attest as the head
attester name = [opengame|

    inputs    : ticker,chainNew,chainOld ;
    feedback  :  ;

    :-----:
    inputs    : ticker,chainNew,chainOld ;
    feedback  :   ;
    operation : dependentDecision name (\(ticker, chainNew, chainOld) -> [1, vertexCount chainNew]) ;
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

updatePayoffProposer name reward  = [opengame|
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
    operation : addPayoffs name ;
    outputs   : ;
    returns   : ;
    // ^ Could make sense to make sense to model this in period
    :-----:

    outputs   : value ;
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

    outputs   : head ;
    returns   :  ;

  |]


proposerPayment name reward = [opengame|

    inputs    : chainNew ;
    feedback  :   ;

    :-----:
    inputs    : chainNew ;
    feedback  :   ;
    operation : forwardFunction proposedCorrect ;
    outputs   : correctSent ;
    returns   : ;
    // ^ This determines whether the proposer was correct in period (t-1)


    inputs    : correctSent ;
    feedback  :   ;
    operation : updatePayoffProposer name reward;
    outputs   : value ;
    returns   : ;
    // ^ Updates the payoff of the proposer given decision in period (t-1)

    :-----:

    outputs   : value ;
    returns   :  ;
  |]



----------------------
-- 2 Group Game blocks

-- Group all attesters together
attestersGroupDecision :: Player
                       -> Player
                       ->  OpenGame
                            StochasticStatefulOptic
                            StochasticStatefulContext
                            ('[Kleisli Stochastic (Timer, Relation (Id, Vote), Chain) Int,
                                Kleisli Stochastic (Timer, Relation (Id, Vote), Chain) Int])
                            ('[[DiagnosticInfoBayesian (Timer, Relation (Id, Vote), Chain) Int],
                                [DiagnosticInfoBayesian (Timer, Relation (Id, Vote), Chain) Int]])
                            (Timer, Relation (Id, Vote), Chain, AttesterMap)
                            ()
                            (AttesterMap, Chain)
                            ()
attestersGroupDecision name1 name2 = [opengame|

    inputs    : ticker,chainNew,chainOld, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker, chainNew, chainOld ;
    feedback  :   ;
    operation : attester name1  ;
    outputs   : attested1 ;
    returns   : ;
    // ^ Attester1 makes a decision

    inputs    : ticker, chainNew, chainOld ;
    feedback  :   ;
    operation : attester name2  ;
    outputs   : attested2 ;
    returns   : ;
    // ^ Attester2 makes a decision

    inputs    : [(name1,attested1),(name2,attested2)], attesterHashMapOld ;
    feedback  : ;
    operation : forwardFunction $ uncurry newAttesterMap ;
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
attestersPayment name1 name2 fee = [opengame|

    inputs    : attesterHashMap, chainNew, headId;
    feedback  :   ;

    :-----:
    inputs    : attesterHashMap, chainNew, headId ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 $ attestedCorrect name1 ;
    outputs   : correctAttested1 ;
    returns   : ;
    // ^ This determines whether attester 1 was correct in period (t-1) using the latest hash and the old information

    inputs    : attesterHashMap, chainNew, headId ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 $ attestedCorrect name2 ;
    outputs   : correctAttested2 ;
    returns   : ;
    // ^ This determines whether attester 2 was correct in period (t-1)


    inputs    : correctAttested1 ;
    feedback  :   ;
    operation : updatePayoffAttester name1 fee ;
    outputs   : ;
    returns   : ;
    // ^ Updates the payoff of attester 1 given decision in period (t-1)

    inputs    : correctAttested2 ;
    feedback  :   ;
    operation : updatePayoffAttester name2 fee ;
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
oneRound p0 p1 a10 a20 a11 a21 reward fee = [opengame|

    inputs    : ticker, delayedTicker, chainOld, attesterHashMapOld  ;
    // ^ chainOld is the old hash
    feedback  :   ;

    :-----:
    inputs    : ticker,delayedTicker,chainOld ;
    feedback  :   ;
    operation : proposer p1;
    outputs   : chainNew, delayedTickerUpdate ;
    returns   : ;
    // ^ Proposer makes a decision, a new hash is proposed

    inputs    : ticker,chainNew,chainOld, attesterHashMapOld;
    feedback  :   ;
    operation : attestersGroupDecision a11 a21 ;
    outputs   : attesterHashMapNew, chainNewUpdated ;
    returns   :  ;
    // ^ Attesters make a decision

    inputs    : chainNewUpdated ;
    feedback  :   ;
    operation : determineHeadOfChain ;
    outputs   : headOfChainId ;
    returns   : ;
    // ^ Determines the head of the chain

    inputs    : attesterHashMapOld, chainNewUpdated, headOfChainId ;
    feedback  :   ;
    operation : attestersPayment a10 a20 fee ;
    outputs   : ;
    returns   : ;
    // ^ Determines whether attesters from period (t-1) were correct and get rewarded

    inputs    : chainNewUpdated ;
    feedback  :   ;
    operation : proposerPayment p0 reward ;
    outputs   : value ;
    returns   : ;
    // ^ This determines whether the proposer from period (t-1) was correct and triggers payments accordingly

    inputs    : value ;
    feedback  :   ;
    operation : debuggingAgent "value for Proposer" ;
    outputs   :  ;
    returns   :  ;

    :-----:

    outputs   : attesterHashMapNew, chainNewUpdated, delayedTickerUpdate ;
    returns   :  ;
  |]



-- Repeated game
repeatedGame  p0 p1 a10 a20 a11 a21 reward fee = [opengame|

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRound p0 p1 a10 a20 a11 a21 reward fee ;
    outputs   : attesterHashMapNew, chainNew, delayedTickerUpdate ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    :-----:

    outputs   : tickerNew, delayedTickerUpdate, chainNew, attesterHashMapNew ;
    returns   :  ;
  |]



twoRoundGame  p0 p1 p2 a10 a20 a11 a21 a12 a22  reward fee = [opengame|

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker,delayedTicker, chainOld, attesterHashMapOld ;
    feedback  :   ;
    operation : oneRound p0 p1 a10 a20 a11 a21 reward fee ;
    outputs   : attesterHashMapNew, chainNew, delayedTickerUpdate ;
    returns   :  ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;

    inputs    : ticker,delayedTicker, chainNew, attesterHashMapNew ;
    // NOTE ticker time is ignored here
    feedback  :   ;
    operation : oneRound p1 p2 a11 a21 a12 a22 reward fee ;
    outputs   : attesterHashMapNew2, chainNew2, delayedTickerUpdate2 ;
    returns   :  ;

    inputs    : tickerNew;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew2;
    returns   : ;



    :-----:

    outputs   : tickerNew2, delayedTickerUpdate2, chainNew2, attesterHashMapNew2 ;
    returns   :  ;
  |]



-- Repeated game
twoRoundGame2 p0 p1 p2 a10 a20 a11 a21 a12 a22  reward fee = [opengame|

    inputs    : ticker1,delayedTicker1,ticker2,delayedTicker2, chainOld, attesterHashMapOld ;
    feedback  :   ;

    :-----:

    inputs    : ticker1,delayedTicker1, chainOld, attesterHashMapOld ;
    feedback  :   ;
    operation : repeatedGame p0 p1 a10 a20 a11 a21 reward fee ;
    outputs   : tickerNew, delayedTickerUpdate, chainNew, attesterHashMapNew ;
    returns   :  ;

    inputs    : ticker2,delayedTicker2, chainNew, attesterHashMapNew ;
    feedback  :   ;
    operation : repeatedGame p1 p2 a11 a21 a12 a22 reward fee ;
    outputs   :  tickerNew2, delayedTickerUpdate2, chainNew2, attesterHashMapNew2 ;
    returns   :  ;

    :-----:

    outputs   :  ;
    returns   :  ;
  |]




----------------
-- Continuations
-- extract continuation
extractContinuation :: StochasticStatefulOptic
                         (Timer, Timer, Chain, M.Map Player Id)
                         ()
                         (Timer, Stochastic Timer, Chain, M.Map Player Id)
                         ()
                    -> (Timer, Stochastic Timer, Chain, M.Map Player Id)
                    -> StateT Vector Stochastic ()
extractContinuation (StochasticStatefulOptic v u) (i, j, chain, map) = do
  j' <- ST.lift j
  let x = (i, j', chain, map)
  (z,a) <- ST.lift (v x)
  u z ()

-- extract next state (action)
extractNextState :: StochasticStatefulOptic
                       (Timer, Timer, Chain, M.Map Player Id)
                       ()
                       (Timer, Stochastic Timer, Chain , M.Map Player Id)
                       ()
                 -> (Timer, Stochastic Timer, Chain, M.Map Player Id)
                 -> Stochastic (Timer, Stochastic Timer, Chain, M.Map Player Id)
extractNextState (StochasticStatefulOptic v _) (i, j, chain, map) = do
  j' <- j
  let x = (i, j', chain, map)
  (z,a) <- v x
  pure a

-- determine continuation for iterator, with the same repeated strategy
determineContinuationPayoffs 1        strat action = pure ()
determineContinuationPayoffs iterator strat action = do
   extractContinuation executeStrat action
   nextInput <- ST.lift $ extractNextState executeStrat action
   determineContinuationPayoffs (pred iterator) strat nextInput
 where executeStrat =  play (repeatedGame "proposer" "proposerPast" "attester1" "attester2" "attester1past" "attester2Past" 2 2) strat


executeStrat strat =  play (repeatedGame "proposer" "proposerPast" "attester1" "attester2" "attester1past" "attester2Past" 2 2) strat

-- fix context used for the evaluation
contextCont iterator strat initialAction = StochasticStatefulContext (pure ((),initialAction)) (\_ action -> determineContinuationPayoffs iterator strat action)