-- | Integer model of a native, fully funded Clipper auction profile.
module JetDiscovery.Ref.Clipper where

import qualified Data.ByteString as BS
import Data.Serialize (putWord32be, runPut)
import qualified JetDiscovery.Ref.Bip340 as R

data State = State
  { active :: Bool
  , lot :: Integer
  , tab :: Integer
  , collected :: Integer
  , initialTab :: Integer
  , epoch :: Integer
  , lastEvent :: Integer
  , initialLot :: Integer
  , identity :: BS.ByteString
  } deriving (Eq, Show)

-- Take carries bidder, requested units, maximum unit price, event clock and
-- quoted curve price. Redo carries the event clock and pre-reset curve price.
data Action = Kick Integer Integer | Take Int Integer Integer Integer Integer | Redo Integer Integer | Yank
  deriving (Eq, Show)
data Payee = Bidder Int | DebtSink | Urn | Ward | SetupSponsor deriving (Eq, Show)
data Output = Continue State | Pay Payee Integer deriving (Eq, Show)

ray, top, tau, tailLimit, cusp, chost :: Integer
ray = 10^27
top = 100
tau = 100
tailLimit = 80
cusp = 40
chost = 1000

lotLimit, debtLimit, eventLimit, collateralUnit, carrier, fee :: Integer
lotLimit = 1000
debtLimit = 100000
eventLimit = 1000000
collateralUnit = 100
carrier = 10000
fee = 1000

setup :: State
setup = State False 0 0 0 0 0 0 0 (BS.replicate 32 0)

fields :: State -> [Integer]
fields state = [if active state then 1 else 0, lot state, tab state, collected state,
  initialTab state, epoch state, lastEvent state, initialLot state]

stateTag, identityTag, actionTag, eventTag :: String
stateTag = "JetDiscovery/Clipper/State"
identityTag = "JetDiscovery/Clipper/Auction"
actionTag = "JetDiscovery/Clipper/Action"
eventTag = "JetDiscovery/Clipper/PriceEvent"

words32 :: [Integer] -> BS.ByteString
words32 = runPut . mapM_ (putWord32be . fromInteger)

stateDigest :: State -> BS.ByteString
stateDigest state = R.taggedHash stateTag (words32 (fields state) <> identity state)

auctionIdentity :: (BS.ByteString, Integer) -> Integer -> Integer -> BS.ByteString
auctionIdentity (rawHash, index) amount debt = R.taggedHash identityTag (rawHash <> words32 [index, amount, debt])

actionFields :: Action -> (Integer, Integer, Integer, Integer, Integer, Integer)
actionFields action = case action of
  Kick amount debt -> (0,0,0,0,amount,debt)
  Take who amount maximumPrice now quote -> (1,toInteger who,now,quote,amount,maximumPrice)
  Redo now quote -> (2,0,now,quote,0,0)
  Yank -> (3,0,0,0,0,0)

actionDigest :: BS.ByteString -> Action -> BS.ByteString
actionDigest transaction action = R.taggedHash actionTag
  (transaction <> BS.pack (map fromInteger [mode, who]) <> words32 [now, quote, amount, cap])
 where (mode, who, now, quote, amount, cap) = actionFields action

eventDigest :: BS.ByteString -> BS.ByteString -> Action -> BS.ByteString
eventDigest transaction auction action = R.taggedHash eventTag
  (transaction <> auction <> BS.singleton (fromInteger mode) <> words32 [now, quote])
 where (mode, _, now, quote, _, _) = actionFields action

stateValue :: State -> Integer
stateValue state = carrier + lot state * collateralUnit

-- Evaluate the pinned calculator at its full RAY scale before normalization.
priceRaw :: Integer -> Integer
priceRaw elapsed
  | elapsed >= tau = 0
  | otherwise = (top * ray) * ((tau - elapsed) * ray `div` tau) `div` ray

needsRedo :: Integer -> Bool
needsRedo elapsed = elapsed > tailLimit || priceRaw elapsed * ray `div` (top * ray) < cusp * ray `div` 100

valid :: State -> Bool
valid state
  | not (active state) = state == setup
  | otherwise = 0 < lot state && lot state <= initialLot state && initialLot state <= lotLimit
    && 0 < tab state && collected state >= 0 && tab state + collected state == initialTab state
    && initialTab state <= debtLimit && 0 <= epoch state && epoch state <= lastEvent state
    && lastEvent state <= eventLimit && BS.length (identity state) == 32

validEvent :: State -> Integer -> Integer -> Bool
validEvent state now quote = lastEvent state <= now && now <= eventLimit
  && priceRaw (now - epoch state) == quote * ray

-- Cap and dust adjust debt at full source scale. Keep adjusted debt when the
-- collateral quotient rounds down. The native profile accepts positive fills.
fill :: Integer -> Integer -> Integer -> Integer -> Maybe (Integer, Integer)
fill remainingLot remainingDebt request elapsed = do
  let price = priceRaw elapsed
      firstSlice = min remainingLot request
      debt = remainingDebt * ray
      preliminary = firstSlice * price
      dust = chost * ray
  (slice, owe) <- if price <= 0 || request <= 0 then Nothing
    else if preliminary > debt then Just (debt `div` price, debt)
    else if preliminary < debt && firstSlice < remainingLot && debt - preliminary < dust
      then if debt <= dust then Nothing else Just ((debt - dust) `div` price, debt - dust)
    else Just (firstSlice, preliminary)
  if slice > 0 && owe > 0 && owe `mod` ray == 0 then Just (slice, owe `div` ray) else Nothing

step :: (BS.ByteString, Integer) -> State -> Action -> Maybe [Output]
step origin state action
  | not (valid state) = Nothing
  | otherwise = case action of
      Kick amount debt | not (active state) && amount > 0 && amount <= lotLimit && debt > 0 && debt <= debtLimit ->
        Just [Continue (State True amount debt 0 debt 0 0 amount (auctionIdentity origin amount debt))]
      Redo now quote | active state && validEvent state now quote && needsRedo (now - epoch state) ->
        Just [Continue state { epoch = now, lastEvent = now }]
      Yank | active state -> Just [Pay Ward (lot state * collateralUnit), Pay SetupSponsor carrier]
      Take who request maximumPrice now quote
        | active state && who `elem` [0,1] && validEvent state now quote && quote <= maximumPrice
          && not (needsRedo (now - epoch state)) -> do
          (slice, owe) <- fill (lot state) (tab state) request (now - epoch state)
          let nextLot = lot state - slice
              nextDebt = tab state - owe
              pay = [Pay (Bidder who) (slice * collateralUnit), Pay DebtSink owe]
              terminal = pay ++ [Pay Urn (nextLot * collateralUnit) | nextLot /= 0] ++ [Pay SetupSponsor carrier]
          if nextLot == 0 || nextDebt == 0 then Just terminal else Just
            (Continue state { lot = nextLot, tab = nextDebt, collected = collected state + owe, lastEvent = now } : pay)
      _ -> Nothing
