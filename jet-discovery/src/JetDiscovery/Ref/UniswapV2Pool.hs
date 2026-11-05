-- | Independent Integer accounting for the pinned Uniswap V2 Pair formulas.
module JetDiscovery.Ref.UniswapV2Pool where

import Data.List (foldl')

data Action = Issue Int Int Integer | Redeem Int Int Integer
            | SetFee Bool | Mint Int Integer Integer | Burn Int Integer
            | Swap Int Int Integer Integer deriving (Eq,Show)

type Ledger = [Integer]
initial :: Ledger
initial = replicate 16 0

cap, minimumLiquidity :: Integer
cap = 2^(22 :: Int)-1
minimumLiquidity = 1000

sqrtInteger :: Integer -> Integer
sqrtInteger x | x<0 = error "sqrt domain"
              | x<=1 = x
              | otherwise = search 0 (x+1)
 where
  search lo hi | hi-lo==1 = lo
               | mid*mid <= x = search mid hi
               | otherwise = search lo mid
   where mid=(lo+hi) `div` 2

-- Pool fields: backing, reserve A/B, A balances [0,1,fee], B balances
-- [0,1,fee], LP balances [0,1,fee], locked liquidity, fee-on, kLast, nonce.
replace :: Ledger -> [(Int,Integer)] -> Ledger
replace = foldl' (\ls (i,x) -> take i ls ++ [x] ++ drop (i+1) ls)

supply :: Ledger -> Integer
supply = sum . take 4 . drop 9

protocolMint :: Ledger -> Integer
protocolMint s | s!!13==0 || s!!14==0 || k<=before = 0
               | otherwise = supply s * (k-before) `div` (5*k+before)
 where
  k=sqrtInteger (s!!1*s!!2)
  before=sqrtInteger (s!!14)

quote :: Ledger -> Int -> Integer -> Integer
quote s side input = input*997*s!!(2-side) `div` (s!!(1+side)*1000+input*997)

step :: Ledger -> Action -> Maybe (Ledger,Integer,Maybe (Int,Integer))
step s action = case action of
  Issue side who amount | role who && asset side && amount>0 ->
    finish [(0,s!!0+amount),(owner side who,s!!owner side who+amount)] amount Nothing
  Redeem side who amount | role who && asset side && amount>0 && amount<=s!!owner side who ->
    finish [(0,s!!0-amount),(owner side who,s!!owner side who-amount)] 0 (Just(who,amount))
  SetFee enabled -> finish [(13,if enabled then 1 else 0)] 0 Nothing
  Mint who a b | role who && a>0 && b>0 && a<=s!!owner 0 who && b<=s!!owner 1 who ->
    let started=supply s>0
        x=s!!1+a; y=s!!2+b
        fee=protocolMint s; total=supply s+fee
        minted=if started then min (a*total `div` s!!1) (b*total `div` s!!2)
                          else sqrtInteger (a*b)-minimumLiquidity
        lp=[(9+i,s!!(9+i)+(if i==2 then fee else 0)+(if i==who then minted else 0))|i<-[0..2]]
    in if minted<=0 then Nothing else finish
         ([(1,x),(2,y),(owner 0 who,s!!owner 0 who-a),(owner 1 who,s!!owner 1 who-b),
           (12,minimumLiquidity),(14,kUpdate x y)]++lp) 0 Nothing
  Burn who n | role who && n>0 && n<=s!!(9+who) ->
    let fee=protocolMint s; total=supply s+fee
        a=n*s!!1 `div` total; b=n*s!!2 `div` total
        x=s!!1-a; y=s!!2-b
        lp=[(9+i,s!!(9+i)+(if i==2 then fee else 0)-(if i==who then n else 0))|i<-[0..2]]
    in if a<=0 || b<=0 then Nothing else finish
         ([(1,x),(2,y),(owner 0 who,s!!owner 0 who+a),(owner 1 who,s!!owner 1 who+b),(14,kUpdate x y)]++lp) 0 Nothing
  Swap side who amount out | role who && asset side && s!!(1+side)>0 && amount>0 &&
                              out>0 && amount<=s!!owner side who && out<s!!(2-side) ->
    let x=s!!(1+side)+amount; y=s!!(2-side)-out
    in if (x*1000-amount*3)*(y*1000)<s!!1*s!!2*1000000 then Nothing else
         finish [(1+side,x),(2-side,y),(owner side who,s!!owner side who-amount),
                  (owner (1-side) who,s!!owner (1-side) who+out)] 0 Nothing
  _ -> Nothing
 where
  role i=i>=0 && i<3
  asset i=i==0 || i==1
  owner side i=3+3*side+i
  kUpdate x y=if s!!13==1 then x*y else 0
  finish changes funding payout =
    let n=replace s ((15,s!!15+1):changes)
    in if sum (n!!1:take 3(drop 3 n))<=cap && sum (n!!2:take 3(drop 6 n))<=cap
       then Just(n,funding,payout) else Nothing
