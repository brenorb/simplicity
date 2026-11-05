-- | Independent integer model of a bounded virtual-reserve launch.
module JetDiscovery.Ref.PumpLaunch
  ( Phase(..), Owner(..), State(..), Action(..), Result(..), setup, encode, value, transition
  , carrier, fee, voucherValue, inventory, migrationInventory, virtualBaseOffset, virtualQuoteOffset
  , migrationFee, maxQuote, sponsor, protocol, destination, referenceAudit
  ) where

import Control.Monad (guard)
import qualified Data.ByteString as BS
import Data.Serialize (putWord32be,runPut)

data Phase = Dormant | Trading | Migrated deriving (Eq,Show,Enum)
data Owner = Alice | Bob deriving (Eq,Show,Enum)
data State = State
  { phase :: Phase, remaining :: Integer, alice :: Integer, bob :: Integer, quote :: Integer
  } deriving (Eq,Show)
data Action = Fund | Buy Owner Integer Integer | Sell Owner Integer Integer
            | Transfer Owner Integer | Migrate | Redeem Owner Integer deriving (Eq,Show)
data Result = Result
  { next :: Maybe State, funding :: Integer, payouts :: [(Int,Integer)], authorizer :: Maybe Int
  } deriving (Eq,Show)

carrier, fee, voucherValue, inventory, migrationInventory, virtualBaseOffset, virtualQuoteOffset :: Integer
carrier = 10000
fee = 1000
voucherValue = 5000
inventory = 100
migrationInventory = 20
virtualBaseOffset = 30
virtualQuoteOffset = 100000

migrationFee, maxQuote :: Integer
migrationFee = 5000
maxQuote = 2000000

sponsor, protocol, destination :: Int
sponsor = 3
protocol = 2
destination = 4

setup :: State
setup = State Dormant 0 0 0 0

encode :: State -> BS.ByteString
encode s = runPut (mapM_ (putWord32be . fromInteger)
  [toInteger (fromEnum (phase s)),remaining s,alice s,bob s,quote s,0,0,0])

value :: State -> Integer
value s = carrier + case phase s of
  Dormant -> 0
  Trading -> quote s + (inventory+migrationInventory)*voucherValue
  Migrated -> (alice s+bob s)*voucherValue

balance :: Owner -> State -> Integer
balance Alice = alice
balance Bob = bob

change :: Owner -> Integer -> State -> State
change Alice delta s = s {alice=alice s+delta}
change Bob delta s = s {bob=bob s+delta}

opposite :: Owner -> Owner
opposite Alice = Bob
opposite Bob = Alice

valid :: State -> Bool
valid s = all (>=0) [remaining s,alice s,bob s,quote s] && quote s<=maxQuote &&
  case phase s of
    Dormant -> s==setup
    Trading -> remaining s+alice s+bob s==inventory
    Migrated -> remaining s==0 && quote s==0 && alice s+bob s>0 && alice s+bob s<=inventory

transition :: State -> Action -> Maybe Result
transition old action = do
  guard (valid old)
  case action of
    Fund | phase old==Dormant ->
      finish (Just (old {phase=Trading,remaining=inventory})) (voucherValue*(inventory+migrationInventory)) [] (Just sponsor)
    Buy who qty maximumCost | open && qty>0 && qty<=remaining old -> do
      let net = div (qty*vx) (vy-qty) + 1
          charge = tradeFee net
      guard (net+charge<=maximumCost)
      finish (Just (change who qty (old {remaining=remaining old-qty,quote=quote old+net})))
        (net+charge) [(protocol,charge)] (owner who)
    Sell who qty minOutput | open && qty>0 && qty<=balance who old -> do
      let gross = div (qty*vx) (vy+qty)
          charge = tradeFee gross
          paid = gross-charge
      guard (gross<=quote old && paid>0 && paid>=minOutput)
      finish (Just (change who (-qty) (old {remaining=remaining old+qty,quote=quote old-gross})))
        0 [(fromEnum who,paid),(protocol,charge)] (owner who)
    Transfer who qty | phase old/=Dormant && qty>0 && qty<=balance who old ->
      finish (Just (change (opposite who) qty (change who (-qty) old))) 0 [] (owner who)
    Migrate | phase old==Trading && remaining old==0 && quote old>migrationFee ->
      finish (Just (old {phase=Migrated,quote=0})) 0
        [(destination,quote old-migrationFee+voucherValue*migrationInventory),(protocol,migrationFee)] Nothing
    Redeem who qty | phase old==Migrated && qty>0 && qty<=balance who old ->
      let s = change who (-qty) old
          payout = (fromEnum who,qty*voucherValue)
      in if alice s+bob s==0 then finish Nothing 0 [payout,(sponsor,carrier)] (owner who)
           else finish (Just s) 0 [payout] (owner who)
    _ -> Nothing
 where
  vx = virtualQuoteOffset+quote old
  vy = virtualBaseOffset+remaining old
  open = phase old==Trading && remaining old>0
  tradeFee n = div (n+99) 100
  owner = Just . fromEnum
  finish target added paid signer = do
    guard (maybe True valid target && all ((>0) . snd) paid)
    guard (value old+added==maybe 0 value target+sum (map snd paid))
    pure (Result target added paid signer)

referenceAudit :: Bool
referenceAudit =
  case transition setup Fund >>= next of
    Just initial ->
      case transition initial (Buy Alice 55 100000) of
        Just (Result (Just bought) gross paid _) ->
          gross==74068 && paid==[(protocol,734)] && quote bought==73334 &&
          case transition bought (Sell Alice 25 40000) of
            Just (Result (Just sold) 0 sellPaid _) ->
              sellPaid==[(0,42899),(protocol,434)] && quote sold==30001 &&
              transition sold Migrate==Nothing
            _ -> False
        _ -> False
    Nothing -> False
