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

module Examples.TimingGames.TimingGame where 


-- TODO Do we need more attesters to make that model relevant?
-- TODO What is the payoff for the sender?

-- DONE We need a stochastic process which delays the signal with some prob, simply correct or delayed after 4 with small prob
-- DONE the payoff needs to come from the future if the block is contained
-- 

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

-- Given a previousString 
createRandomString :: Int -> String -> Stochastic String
createRandomString 0 str = do
  r <- uniformDist ["abc","def","ghi"]
  pure (r ++ str)
createRandomString _ str = playDeterministically str


transformTicker :: Int -> Int
transformTicker 12 = 0
transformTicker x  = x + 1

-- Has the attester correctly verified the hash?
-- TODO Not clear exactly what "correct" means. Correct in the sense of the protocol I guess.
attestedCorrect hashOld hashNew = isInfixOf hashOld hashNew


-- draw from a timer which determines whether the message is delayed
delaySendTime :: Int -> Int ->  Stochastic Int
delaySendTime actualTimer delayedTimer
  | actualTimer ==  0       = distFromList [(0,0.5),(5,0.5)]
  | delayedTimer == 5 = playDeterministically delayedTimer
  | otherwise         = playDeterministically actualTimer

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



---------------------
-- 1 Game blocks
-- A proposer observes the ticker and decides to send the block or not
-- If the block is sent, the exogenous block is sent, otherwise the empty string
-- There is a delayed built in, determined at t=0. If true the new message is not sent but the old message is.
proposer  payoffProposer = [opengame|

    inputs    : ticker, delayedTicker, hashOld ;
    feedback  :   ;

    :-----:
    inputs    : ticker, hashOld ;
    feedback  :   ;
    operation : hashGenerator ;
    outputs   : proposedHash;
    returns   : ;


    inputs    : ticker ;
    feedback  :   ;
    operation : dependentDecision "proposer" (const [Send,DoNotSend]) ;
    outputs   : sent ;
    returns   : payoffProposer sent ticker;
    // ^ decision whether to send the correct message or not

    inputs    : hashOld, proposedHash, sent ;
    feedback  :   ;
    operation : forwardFunction $ uncurry3 sendHash ;
    outputs   : hashNew ;
    returns   : ;
    // ^ if the proposer decided to send the message, update block, else keep the old block

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
    // ^ if correct message is sent update block

    :-----:

    outputs   : messageSent, delayedTickerUpdate ;
    returns   :      ;
  |]

-- The attester observes the sent hash, observes the timer, and can then decide whether to send the hash or not
attester payoffAttester = [opengame|

    inputs    : ticker,hash ;
    feedback  :   ;

    :-----:
    inputs    : ticker, hash ;
    feedback  :   ;
    operation : dependentDecision "attester" (\(ticker, hash) -> [HashBlock hash,Empty]) ;
    outputs   : attested ;
    returns   : payoffAttester correctAttestedNew ;

    :-----:

    outputs   : attested ;
    returns   : correctAttestedNew  ;
  |]

-- Generate hash given previous information
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



  
-------------------
-- 2 Complete games
-------------------

-- One round game
oneRound payoffProposer payoffAttester = [opengame|

    inputs    : ticker, delayedTicker, blockHash, attesterHash ;
    feedback  : correctAttested  ;

    :-----:
    inputs    : ticker,delayedTicker,blockHash ;
    feedback  :   ;
    operation : proposer payoffProposer ;
    outputs   : hashNew, delayedTickerUpdate ;
    returns   : ;

    inputs    : attesterHash, hashNew ;
    feedback  :   ;
    operation : forwardFunction $ uncurry attestedCorrect ;
    outputs   : correctAttested ;
    returns   : ;
    // ^ this block needs to change, currently completely deterministic in the detection

    inputs    : ticker, hashNew ;
    feedback  :   ;
    operation : attester payoffAttester ;
    outputs   : attested ;
    returns   : correctAttestedNew;

    :-----:

    outputs   : attested, delayedTickerUpdate ;
    returns   : correctAttestedNew ;
  |]

-- Repeated game
repeatedGame payoffProposer payoffAttester = [opengame|

    inputs    : ticker,delayedTicker, blockHash, attesterHash ;
    feedback  : correctAttestedOld  ;

    :-----:
    inputs    : ticker,delayedTicker, blockHash, attesterHash ;
    feedback  : correctAttestedOld  ;
    operation : oneRound payoffProposer payoffAttester ;
    outputs   : attested, delayedTickerUpdate ;
    returns   : correctAttestedNew ;

    inputs    : ticker;
    feedback  :   ;
    operation : forwardFunction transformTicker ;
    outputs   : tickerNew;
    returns   : ;


    :-----:

    outputs   : tickerNew, delayedTickerUpdate, attested ;
    returns   : correctAttestedNew         ;
  |]

