-- | Independent ownership and Bitcoin cash model for the TwoCrypto profile.
module JetDiscovery.Ref.TwoCryptoLedger
  ( Owner(..), Asset(..), State(..), Account(..), Action(..), Result(..)
  , carrier, fee, maxCollateral, setup, ledger, transition, signer, maturity
  ) where

import Control.Monad (guard)
import qualified JetDiscovery.Ref.TwoCrypto as M

data Owner = Alice | Bob deriving (Eq,Show,Enum)
data Asset = X | Y deriving (Eq,Show,Enum)
data Account = Account Integer Integer Integer deriving (Eq,Show)
data State = State
  { pool :: M.Pool
  , alice :: Account
  , bob :: Account
  , administrator :: (Integer,Integer)
  , nonce :: Integer
  } deriving (Eq,Show)
data Action = Issue Owner Asset Integer | Transfer Owner Asset Integer
            | Redeem Owner Asset Integer | Join Owner (Integer,Integer)
            | Swap Owner Asset Integer | Exit Owner Integer | MoveLp Owner Integer
            | Sweep | RedeemFee Asset Integer deriving (Eq,Show)
data Result = Result
  { next :: State
  , funded :: Integer
  , payout :: Maybe (Int,Integer)
  } deriving (Eq,Show)

carrier, fee, maxCollateral :: Integer
carrier = 10000
fee = 1000
maxCollateral = 20000000

maturity :: Asset -> Integer
maturity X = 800000
maturity Y = 900000

setup :: State
setup = State M.empty (Account 0 0 0) (Account 0 0 0) (0,0) 0

ledger :: State -> [Integer]
ledger s =
  [totalX+totalY,totalX,totalY,aX,bX,aY,bY,x,y,feeX,feeY,M.supply p,aLp,bLp,nonce s,
   M.storedD p,M.virtualPrice p,M.profit p,M.profitAnchor p,M.adminCredit p] ++ replicate 12 0
 where
  p = pool s
  (x,y) = M.reserves p
  (feeX,feeY) = administrator s
  Account aX aY aLp = alice s
  Account bX bY bLp = bob s
  totalX = aX+bX+x+feeX
  totalY = aY+bY+y+feeY

ownerIndex :: Owner -> Int
ownerIndex = fromEnum

other :: Owner -> Owner
other Alice = Bob
other Bob = Alice

account :: Owner -> State -> Account
account Alice = alice
account Bob = bob

change :: Owner -> (Account -> Account) -> State -> State
change Alice f s = s {alice=f (alice s)}
change Bob f s = s {bob=f (bob s)}

coin :: Asset -> Account -> Integer
coin X (Account a _ _) = a
coin Y (Account _ b _) = b

credit :: Asset -> Integer -> Account -> Account
credit X n (Account a b lp) = Account (a+n) b lp
credit Y n (Account a b lp) = Account a (b+n) lp

liquidity :: Account -> Integer
liquidity (Account _ _ lp) = lp

creditLp :: Integer -> Account -> Account
creditLp n (Account a b lp) = Account a b (lp+n)

creditCoins :: (Integer,Integer) -> Account -> Account
creditCoins (a,b) = credit X a . credit Y b

signer :: Action -> Int
signer action = case action of
  Issue who _ _ -> ownerIndex who
  Transfer who _ _ -> ownerIndex who
  Redeem who _ _ -> ownerIndex who
  Join who _ -> ownerIndex who
  Swap who _ _ -> ownerIndex who
  Exit who _ -> ownerIndex who
  MoveLp who _ -> ownerIndex who
  Sweep -> 3
  RedeemFee _ _ -> 3

valid :: State -> Bool
valid s = all (\x -> 0 <= x && x < 2^64) (ledger s) &&
  sum [liquidity (alice s),liquidity (bob s)] == M.supply p &&
  head (ledger s) <= maxCollateral &&
  M.wad <= M.virtualPrice p && M.virtualPrice p <= 2*M.wad &&
  M.wad <= M.profitAnchor p && M.profitAnchor p <= M.profit p && M.profit p <= 4*M.wad &&
  M.adminCredit p <= 8*M.wad && M.supply p <= 8*M.wad &&
  if M.supply p==0
    then M.reserves p==(0,0) && M.storedD p==0
    else all (\x -> M.minReserve<=x && x<=M.maxReserve) [fst (M.reserves p),snd (M.reserves p)] &&
         10^17 <= M.storedD p && M.storedD p <= 8*M.wad
 where p = pool s

transition :: State -> Action -> Maybe Result
transition old action = do
  guard (valid old)
  case action of
    Issue who asset amount | amount>0 ->
      finish (change who (credit asset amount) old) amount Nothing
    Transfer who asset amount | affordable who asset amount ->
      finish (change (other who) (credit asset amount) (change who (credit asset (negate amount)) old)) 0 Nothing
    Redeem who asset amount | affordable who asset amount ->
      finish (change who (credit asset (negate amount)) old) 0 (Just (ownerIndex who,amount))
    Join who amounts@(a,b) -> do
      guard (a>=0 && b>=0 && coin X (account who old)>=a && coin Y (account who old)>=b)
      (p,minted,_) <- M.join (pool old) amounts
      finish (change who (creditCoins (-a,-b) . creditLp minted) (old {pool=p})) 0 Nothing
    Swap who input amount | affordable who input amount -> do
      (p,output,_) <- M.swap (pool old) (fromEnum input) amount
      let outputAsset = if input==X then Y else X
      finish (change who (credit input (negate amount) . credit outputAsset output) (old {pool=p})) 0 Nothing
    Exit who amount | amount>0 && liquidity (account who old)>=amount -> do
      (p,amounts) <- M.exit (pool old) amount
      finish (change who (creditLp (negate amount) . creditCoins amounts) (old {pool=p})) 0 Nothing
    MoveLp who amount | amount>0 && liquidity (account who old)>=amount ->
      finish (change (other who) (creditLp amount) (change who (creditLp (negate amount)) old)) 0 Nothing
    Sweep -> do
      (p,(a,b)) <- M.sweep (pool old)
      let (ax,ay) = administrator old
      finish (old {pool=p,administrator=(ax+a,ay+b)}) 0 Nothing
    RedeemFee asset amount | amount>0 ->
      let (a,b) = administrator old
          next = if asset==X then (a-amount,b) else (a,b-amount)
      in finish (old {administrator=next}) 0 (Just (3,amount))
    _ -> Nothing
 where
  affordable who asset amount = amount>0 && coin asset (account who old)>=amount
  finish s fund pay = do
    let next = s {nonce=nonce old+1}
    guard (valid next && head (ledger old)+fund==head (ledger next)+maybe 0 snd pay)
    pure (Result next fund pay)
