-- | Integer model of the bounded, funded CQF round. The paper specifies the
-- alpha mixture. The cap, floor and sponsor remainder are native policy.
module JetDiscovery.Ref.QuadraticFunding
  ( State(..), Action(..), Step(..), Voice3, Claims, cap, maxBudget, fee
  , initial, balance, allocation, apply, encode, referenceAudit ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C
import Data.List (permutations)
import Data.Serialize (putWord8, putWord16be, putWord64be, runPut)

type Voice3 = (Integer,Integer,Integer)
type Claims = (Integer,Integer,Integer)
data State = Open Integer Voice3 Voice3 | Closed Claims deriving (Eq,Show)
data Action = Donate Int Integer | Close | Claim Int deriving (Eq,Show)
data Step = Step
  { successor :: Maybe State
  , donorDebit :: Integer
  , payment :: Maybe (Int,Integer)
  } deriving (Eq,Show)

cap, maxBudget, fee :: Integer
cap = 63
maxBudget = 65535
fee = 1000

unpack :: (a,a,a) -> [a]
unpack (a,b,c) = [a,b,c]

triple :: [a] -> (a,a,a)
triple [a,b,c] = (a,b,c)
triple _ = error "quadratic funding requires three fixed slots"

initial :: Integer -> State
initial b = Open b (0,0,0) (0,0,0)

cost :: Voice3 -> Integer
cost = sum . map (^ (2 :: Int)) . unpack

balance :: State -> Integer
balance (Open b a c) = b + cost a + cost c
balance (Closed p) = sum (unpack p)

valid :: State -> Bool
valid (Open b a c) = 1 <= b && b <= maxBudget && all (\v -> 0 <= v && v <= cap) (unpack a ++ unpack c)
valid (Closed (p,q,r)) = all (\v -> 0 <= v && v <= (3*cap)^ (2 :: Int)) [p,q]
                         && 0 <= r && r <= maxBudget

allocation :: Integer -> Voice3 -> Voice3 -> Claims
allocation b a c = (cost a + m a, cost c + m c, b - m a - m c)
 where
  -- Independent pair-product form of the matching deficit.
  deficit (x,y,z) = 2 * (x*y + x*z + y*z)
  d = deficit a + deficit c
  m v | d == 0 = 0
      | otherwise = (min b d * deficit v) `div` d

apply :: State -> Action -> Maybe Step
apply old action
  | not (valid old) = Nothing
  | otherwise = case (old,action) of
      (Open b a c, Donate slot next)
        | slot >= 0 && slot < 6 && oldVoice < next && next <= cap ->
            let (first,second) = splitAt 3 [if j==slot then next else v | (j,v) <- zip [0..] votes]
                new = Open b (triple first) (triple second)
            in Just (Step (Just new) (next*next-oldVoice*oldVoice) Nothing)
       where votes = unpack a ++ unpack c
             oldVoice = votes !! slot
      (Open b a c, Close) -> Just (Step (Just (Closed (allocation b a c))) 0 Nothing)
      (Closed p, Claim slot)
        | slot >= 0 && slot < 3 && xs !! slot > 0 ->
          let left = [if j==slot then 0 else v | (j,v) <- zip [0..] xs]
          in Just (Step (if sum left==0 then Nothing else Just (Closed (triple left)))
                        0 (Just (slot,xs !! slot)))
       where xs = unpack p
      _ -> Nothing

encode :: State -> BS.ByteString
encode state = C.pack "QF-BTC-Round-v1!" <> runPut (case state of
  Open b a c -> do
    putWord64be 0
    putWord16be (fromInteger b)
    mapM_ (putWord8 . fromInteger) (unpack a ++ unpack c)
  Closed (a,b,c) -> do
    putWord64be 1
    mapM_ (putWord16be . fromInteger) [a,b,c,0])

referenceAudit :: Bool
referenceAudit = and
  [ allocation 1001 (20,20,0) (20,10,0) == (1467,833,1)
  , allocation 2000 (20,20,0) (20,10,0) == (1600,900,800)
  , allocation 1001 (20,0,0) (0,0,10) == (400,100,1001)
  , allocation 65535 (63,63,63) (63,63,63) == (35721,35721,17907)
  , apply (initial 1001) (Donate 0 20) == Just (Step (Just (Open 1001 (20,0,0) (0,0,0))) 400 Nothing)
  , apply (Open 1001 (20,0,0) (0,0,0)) (Donate 0 21) == Just (Step (Just (Open 1001 (21,0,0) (0,0,0))) 41 Nothing)
  , all claimsConserve (permutations [0,1,2])
  , apply (Closed (0,1,0)) (Claim 0) == Nothing
  , apply (Closed (0,1,0)) Close == Nothing
  , apply (initial 1001) (Donate 6 1) == Nothing
  , apply (initial 1001) (Donate 0 64) == Nothing
  , BS.length (encode (initial 1001)) == 32
  , BS.length (encode (Closed (1,2,3))) == 32
  ]
 where
  claimsConserve order = loop (Closed (1467,833,1)) order 0
  loop s (i:is) paid = case apply s (Claim i) of
    Just (Step (Just n) 0 (Just (j,x))) -> i==j && balance n+x==balance s && loop n is (paid+x)
    Just (Step Nothing 0 (Just (j,x))) -> i==j && null is && x==balance s && paid+x==2301
    _ -> False
  loop _ [] _ = False
