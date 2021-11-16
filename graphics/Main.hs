{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Preprocessor.THSyntax
import Preprocessor.TH
import Preprocessor.AbstractSyntax
import Preprocessor.Compile
import Graphics as Gfx
import System.Process.Typed

import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import Data.GraphViz.Commands.IO


customParams :: GraphvizParams n String Gfx.ArrowType () String
customParams = let rec = quickParams :: GraphvizParams n String Gfx.ArrowType () String in
                   rec { fmtNode = \x -> Shape BoxShape : (fmtNode rec x)
                       , fmtEdge = \case (_, _, (Contravariant lbl)) -> [Label $ toLabelValue lbl, Style [SItem Dotted []]]
                                         (_, _, Covariant lbl) -> [Label $ toLabelValue lbl, Style [SItem Solid []]]
                                         (_, _, Gfx.Both lbl) -> [Label $ toLabelValue lbl, Style [SItem Dotted [], SItem Solid []]] }


---------------------
-- 1 Game blocks

-- Generate hash given previous information
-- At time t=0 a new string is generated; otherwise the same old string is still used
hashGenerator = [parseTree|

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
proposer   = [parseTree|

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
attester  = [parseTree|

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
    :-----:

    outputs   : attested ;
    returns   :  ;
  |]

-- attesterPayoff fee correctAttestedNew ;
-- proposerPayoff reward correctSent ;

updatePayoffAttester   = [parseTree|
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

updatePayoffProposer    = [parseTree|
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

oneRound  = [parseTree|

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
repeatedGame  = [parseTree|

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



main :: IO ()
main = do
  writeDotFile "hashGenerator" (graphToDot customParams (convertBlock hashGenerator))
  writeDotFile "proposer" (graphToDot customParams (convertBlock proposer))
  writeDotFile "attester" (graphToDot customParams (convertBlock attester))
  writeDotFile "updatePayoffAttester" (graphToDot customParams (convertBlock updatePayoffAttester))
  writeDotFile "updatePayoffProposer" (graphToDot customParams (convertBlock updatePayoffProposer))
  writeDotFile "oneRound" (graphToDot customParams (convertBlock oneRound))
  writeDotFile "repeatedGame" (graphToDot customParams (convertBlock repeatedGame))
  runProcess_
      (shell
          ( "dot -Tsvg hashGenerator > hashGenerator.svg ")
          )
  runProcess_
      (shell
          ( "dot -Tsvg proposer > proposer.svg ")
          )
  runProcess_
      (shell
          ( "dot -Tsvg attester > attester.svg ")
          )
  runProcess_
      (shell
          ( "dot -Tsvg updatePayoffAttester > updatePayoffAttester.svg ")
          )
  runProcess_
      (shell
          ( "dot -Tsvg updatePayoffProposer > updatePayoffProposer.svg ")
          )
  runProcess_
      (shell
          ( "dot -Tsvg repeatedGame > repeatedGame.svg ")
          )
