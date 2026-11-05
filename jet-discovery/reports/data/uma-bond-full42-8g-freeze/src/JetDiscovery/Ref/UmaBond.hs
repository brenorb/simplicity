-- | Integer accounting and byte transcripts for the bounded native OOv3 model.
module JetDiscovery.Ref.UmaBond where

import qualified Data.ByteString as BS
import Data.Serialize (putWord32be, putWord64be, runPut)
import qualified JetDiscovery.Ref.Bip340 as R

data Phase = Setup | Asserted | Challenged deriving (Eq, Show, Enum)

data State = State
  { phase :: Phase
  , bond :: Integer
  , assertion :: BS.ByteString
  } deriving (Eq, Show)

data Action = Assert BS.ByteString Integer | Challenge | Refund Integer | Resolve Bool
  deriving (Eq, Show)

data Payee = Asserter | Challenger | Store | SetupSponsor deriving (Eq, Show)
data Destination = Continue State | Pay Payee Integer deriving (Eq, Show)

minimumBond, maximumBond, carrier, fee, delay :: Integer
minimumBond = 2000
maximumBond = 1000000
carrier = 10000
fee = 1000
delay = 10

setup :: State
setup = State Setup 0 (BS.replicate 32 0)

validBond :: Integer -> Bool
validBond amount = minimumBond <= amount && amount <= maximumBond

validState :: State -> Bool
validState state
  | phase state == Setup = state == setup
  | otherwise = validBond (bond state) && BS.length (assertion state) == 32

stateValue :: State -> Integer
stateValue state = carrier + case phase state of
  Setup -> 0
  Asserted -> bond state
  Challenged -> 2 * bond state

storeFee :: Integer -> Integer
storeFee amount = amount `div` 2

stateTag, assertionTag, verdictTag :: String
stateTag = "JetDiscovery/UmaOOv3/State"
assertionTag = "JetDiscovery/UmaOOv3/Assertion"
verdictTag = "JetDiscovery/UmaOOv3/Verdict"

word64 :: Integer -> BS.ByteString
word64 = runPut . putWord64be . fromInteger

assertionDigest :: BS.ByteString -> Integer -> (BS.ByteString, Integer) -> BS.ByteString
assertionDigest claim amount (rawHash, index) = R.taggedHash assertionTag
  (claim <> word64 amount <> rawHash <> runPut (putWord32be (fromInteger index)))

stateDigest :: State -> BS.ByteString
stateDigest state = R.taggedHash stateTag
  (BS.singleton (fromIntegral (fromEnum (phase state))) <> word64 (bond state) <> assertion state)

verdictDigest :: BS.ByteString -> Bool -> BS.ByteString -> BS.ByteString
verdictDigest claimIdentity outcome transaction = R.taggedHash verdictTag
  (claimIdentity <> BS.singleton (if outcome then 1 else 0) <> transaction)

transition :: (BS.ByteString, Integer) -> State -> Action -> Maybe [Destination]
transition genesis state action
  | not (validState state) = Nothing
  | otherwise = case (phase state, action) of
      (Setup, Assert claim amount)
        | BS.length claim == 32 && validBond amount ->
          Just [Continue (State Asserted amount (assertionDigest claim amount genesis))]
      (Asserted, Challenge) -> Just [Continue state { phase = Challenged }]
      (Asserted, Refund sequenceDistance)
        | sequenceDistance >= delay -> Just [Pay Asserter (bond state), Pay SetupSponsor carrier]
      (Challenged, Resolve outcome) ->
        let feeAmount = storeFee (bond state)
            winner = if outcome then Asserter else Challenger
        in Just [Pay winner (2 * bond state - feeAmount), Pay Store feeAmount, Pay SetupSponsor carrier]
      _ -> Nothing
