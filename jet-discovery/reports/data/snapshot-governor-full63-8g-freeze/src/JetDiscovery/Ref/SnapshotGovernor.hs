-- | Integer reference for a single snapshot-weighted native proposal.
module JetDiscovery.Ref.SnapshotGovernor where

import qualified Data.ByteString as BS
import Data.Bits (setBit, testBit)
import Data.Serialize (putWord16be, runPut)
import qualified JetDiscovery.Ref.Bip340 as R

data State = State
  { clock :: Integer
  , balances :: [Integer]
  , delegates :: [Int]
  , phase :: Int
  , snapshot :: Integer
  , weights :: [Integer]
  , voted :: Int
  , tallies :: [Integer]
  , proposalAmount :: Integer
  } deriving (Eq, Show)

data Action = Transfer Int Int Integer | Delegate Int Int | Propose Int Int Integer
            | Vote Int Int | Tick | Queue | Execute | Recover deriving (Eq, Show)

data Payee = Target Int | Treasury deriving (Eq, Show)
data Output = Continue State | Pay Payee Integer deriving (Eq, Show)

supply, quorumNumerator, quorumDenominator, period, maxPending :: Integer
supply = 301
quorumNumerator = 40
quorumDenominator = 100
period = 6
maxPending = 60000

treasury, fee, minimumPayment, maximumPayment :: Integer
treasury = 100000
fee = 1000
minimumPayment = 2000
maximumPayment = 50000

initial :: State
initial = State 1 [101,100,100] [0,1,2] 0 0 [0,0,0] 0 [0,0,0] 0

stateTag :: String
stateTag = "JetDiscovery/SnapshotGovernor/State"

actionTag :: String
actionTag = "JetDiscovery/SnapshotGovernor/Action"

actionFields :: Action -> (Integer, Integer, Integer, Integer)
actionFields action = case action of
  Transfer source dest amount -> fieldsFor 0 source dest amount
  Delegate source dest -> fieldsFor 1 source dest 0
  Propose source dest amount -> fieldsFor 2 source dest amount
  Vote voter support -> fieldsFor 3 voter support 0
  Tick -> (4,0,0,0)
  Queue -> (5,0,0,0)
  Execute -> (6,0,0,0)
  Recover -> (7,0,0,0)
 where fieldsFor op who selection amount = (op, toInteger who, toInteger selection, amount)

actionDigest :: BS.ByteString -> Action -> BS.ByteString
actionDigest txMessage action = R.taggedHash actionTag (txMessage <> BS.singleton (fromInteger op)
  <> runPut (mapM_ (putWord16be . fromInteger) [who, selection, amount]))
 where (op, who, selection, amount) = actionFields action

stateDigest :: State -> BS.ByteString
stateDigest state = R.taggedHash stateTag (runPut (mapM_ (putWord16be . fromInteger) (fields state)))

fields :: State -> [Integer]
fields state = [clock state] ++ balances state ++ map toInteger (delegates state) ++
  [toInteger (phase state), snapshot state] ++ weights state ++ [toInteger (voted state)] ++
  tallies state ++ [proposalAmount state]

power :: State -> [Integer]
power state = [sum [amount | (amount, delegate) <- zip (balances state) (delegates state), delegate == who]
  | who <- [0,1,2]]

quorum :: Integer -> Integer
quorum voteSupply = voteSupply * quorumNumerator `div` quorumDenominator

successful :: State -> Bool
successful state = support + abstain >= quorum supply && support > against
 where [against,support,abstain] = tallies state

active :: State -> Bool
active state = phase state `elem` [1,2]

live :: State -> Bool
live state = active state && clock state > snapshot state && clock state <= snapshot state + period

expired :: State -> Bool
expired state = active state && clock state == snapshot state + period + 1

validPayment :: Integer -> Bool
validPayment amount = minimumPayment <= amount && amount <= maximumPayment

valid :: State -> Bool
valid state = clock state >= 1 && length (balances state) == 3 && all (>= 0) (balances state)
  && sum (balances state) == supply && length (delegates state) == 3 && all (`elem` [0..3]) (delegates state)
  && length (weights state) == 3 && length (tallies state) == 3 && case phase state of
    0 -> clock state <= maxPending && all (== 0) (drop 8 (fields state))
    p | p `elem` [1..4] -> proposalFields && if active state
          then clock state <= snapshot state + period + 1
          else clock state == snapshot state + period + 2 && successful state
    _ -> False
 where
  proposalFields = snapshot state >= 1 && snapshot state <= maxPending && snapshot state < clock state
    && validPayment (proposalAmount state) && all (>= 0) (weights state) && sum (weights state) <= supply
    && voted state `elem` [0..7] && all (>= 0) (tallies state)
    && sum (tallies state) == sum [amount | (index, amount) <- zip [0..] (weights state), testBit (voted state) index]

step :: State -> Action -> Integer -> Maybe [Output]
step state action age
  | not (valid state) = Nothing
  | otherwise = case action of
      Transfer source dest amount | mutable && account source && account dest && source /= dest
        && amount > 0 && amount <= balances state !! source ->
          next state { balances = [balance + if index == source then -amount else if index == dest then amount else 0
            | (index,balance) <- zip [0..] (balances state)] }
      Delegate source dest | mutable && account source && dest `elem` [0..3] && delegates state !! source /= dest ->
          next state { delegates = [if index == source then dest else previous
            | (index,previous) <- zip [0..] (delegates state)] }
      Propose source dest amount | phase state == 0 && account source && dest `elem` [0,1] && validPayment amount ->
          next state { phase = dest + 1, snapshot = clock state, weights = power state, proposalAmount = amount }
      Vote voter kind | live state && account voter && account kind && not (testBit (voted state) voter) ->
          next state { voted = setBit (voted state) voter,
            tallies = [total + if index == kind then weights state !! voter else 0
              | (index,total) <- zip [0..] (tallies state)] }
      Tick | live state && age >= 1 -> next state
      Queue | expired state && successful state -> next state { phase = phase state + 2 }
      Execute | phase state `elem` [3,4] && age >= 2 ->
          Just [Pay (Target (phase state - 3)) (proposalAmount state), Pay Treasury (treasury - proposalAmount state)]
      Recover | expired state && not (successful state) -> Just [Pay Treasury treasury]
      _ -> Nothing
 where
  account who = who `elem` [0..2]
  mutable = (phase state == 0 && clock state < maxPending) || live state
  next newState = Just [Continue newState { clock = clock state + 1 }]
