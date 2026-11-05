-- | Integer model of a funded Sablier linear cliff stream adapted to native BTC.
-- The pinned LockupMath formula is evaluated in block-height units.
module JetDiscovery.Ref.SablierStream where

import qualified Data.ByteString as BS
import Data.Serialize (putWord32be, putWord64be, runPut)
import qualified JetDiscovery.Ref.Bip340 as R

data Phase = Pending | Live | Canceled deriving (Eq, Show, Enum)

data State = State
  { phase :: Phase
  , owner :: Integer
  , lastHeight :: Integer
  , withdrawn :: Integer
  , refunded :: Integer
  } deriving (Eq, Show)

data Action = Fund | Withdraw Integer Integer | Transfer | Cancel Integer
  deriving (Eq, Show)

data Payee = Sender | Recipient Integer deriving (Eq, Show)

data Destination = Continuation State | Payout Payee Integer
  deriving (Eq, Show)

deposit, startUnlock, cliffUnlock, startHeight, cliffHeight, endHeight, granularity :: Integer
deposit = 37111
startUnlock = 2500
cliffUnlock = 4600
startHeight = 800000
cliffHeight = 800011
endHeight = 800050
granularity = 7

carrier, fee, heightLimit :: Integer
carrier = 10000
fee = 1000
heightLimit = 500000000

pending, funded :: State
pending = State Pending 0 0 0 0
funded = pending { phase = Live }

streamedAt :: Integer -> Integer
streamedAt height
  | height < startHeight = 0
  | height < cliffHeight = startUnlock
  | height >= endHeight = deposit
  | otherwise = unlocked + (elapsedSteps * streamable * granularity) `div` duration
 where
  unlocked = startUnlock + cliffUnlock
  streamable = deposit - unlocked
  elapsedSteps = (height - cliffHeight) `div` granularity
  duration = endHeight - cliffHeight

remaining :: State -> Integer
remaining state
  | phase state == Pending = 0
  | otherwise = deposit - withdrawn state - refunded state

valid :: State -> Bool
valid state = case phase state of
  Pending -> state == pending
  Live -> liveFields && refunded state == 0
  Canceled -> liveFields && refunded state > 0
 where
  liveFields = owner state `elem` [0, 1] && validHeight (lastHeight state)
    && withdrawn state >= 0 && refunded state >= 0 && remaining state > 0

validHeight :: Integer -> Bool
validHeight height = 0 <= height && height < heightLimit

-- The returned destinations are the complete ordered output list. Both the
-- state amount and terminal carrier ownership are explicit native policy.
transition :: State -> Action -> Maybe [Destination]
transition state action
  | not (valid state) = Nothing
  | otherwise = case (phase state, action) of
      (Pending, Fund) -> Just [Continuation funded]
      (Live, Withdraw height amount)
        | validHeight height && height >= lastHeight state ->
            withdraw (streamedAt height - withdrawn state) height amount
      (Canceled, Withdraw height amount)
        | validHeight height -> withdraw (remaining state) (lastHeight state) amount
      (Live, Transfer) -> transfer
      (Canceled, Transfer) -> transfer
      (Live, Cancel height)
        | height > 0 && validHeight height && height >= lastHeight state
          && streamedAt height >= withdrawn state && streamedAt height < deposit ->
          let refund = deposit - streamedAt height
              credit = streamedAt height - withdrawn state
              next = state { phase = Canceled, lastHeight = height, refunded = refund }
          in Just $ if credit == 0
               then [Payout Sender (refund + carrier)]
               else [Continuation next, Payout Sender refund]
      _ -> Nothing
 where
  transfer = Just [Continuation state { owner = 1 - owner state }]
  withdraw available height amount
    | amount <= 0 || amount > available = Nothing
    | amount == remaining state = Just [Payout (Recipient (owner state)) amount, Payout Sender carrier]
    | otherwise = Just
        [ Continuation state { lastHeight = height, withdrawn = withdrawn state + amount }
        , Payout (Recipient (owner state)) amount
        ]

stateTag, valuationTag :: String
stateTag = "JetDiscovery/Sablier/State"
valuationTag = "JetDiscovery/Sablier/CancellationHeight"

stateDigest :: State -> BS.ByteString
stateDigest state = R.taggedHash stateTag $ BS.concat
  [ BS.pack [fromIntegral (fromEnum (phase state)), fromInteger (owner state)]
  , runPut (putWord32be (fromInteger (lastHeight state)))
  , runPut (putWord64be (fromInteger (withdrawn state)))
  , runPut (putWord64be (fromInteger (refunded state)))
  ]

valuationDigest :: BS.ByteString -> Integer -> BS.ByteString
valuationDigest txMessage height = R.taggedHash valuationTag
  (txMessage <> runPut (putWord32be (fromInteger height)))
