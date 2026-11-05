-- | Integer model of a fixed-scale projection of Curve TwoCrypto NG.
module JetDiscovery.Ref.TwoCrypto
  ( wad, precision, ann, gamma, maxSteps, minReserve, maxReserve
  , Pool(..), empty, invariant, fallbackY, sourceDiscriminant, dynamicFee
  , join, swap, exit, sweep, referenceAudit
  ) where

import Control.Monad (guard)

wad, precision, ann, gamma, minReserve, maxReserve :: Integer
wad = 10^18
precision = 10^12
ann = 4000000
gamma = 199*10^15
minReserve = 100000
maxReserve = 4000000

maxSteps :: Int
maxSteps = 12

midFee, outFee, feeGamma, feeBase :: Integer
midFee = 30000000
outFee = 50000000
feeGamma = 10^16
feeBase = 10^10

data Pool = Pool
  { reserves :: (Integer,Integer)
  , storedD :: Integer
  , supply :: Integer
  , virtualPrice :: Integer
  , profit :: Integer
  , profitAnchor :: Integer
  , adminCredit :: Integer
  } deriving (Eq,Show)

empty :: Pool
empty = Pool (0,0) 0 0 wad wad wad 0

both :: (a -> Bool) -> (a,a) -> Bool
both f (a,b) = f a && f b

mapPair :: (a -> b) -> (a,a) -> (b,b)
mapPair f (a,b) = (f a,f b)

zipPair :: (a -> b -> c) -> (a,a) -> (b,b) -> (c,c)
zipPair f (a,b) (c,d) = (f a c,f b d)

sumPair :: (Integer,Integer) -> Integer
sumPair (a,b) = a+b

normalized :: (Integer,Integer) -> (Integer,Integer)
normalized = mapPair (*precision)

within :: Integer -> Integer -> Integer -> Bool
within lo hi x = lo <= x && x <= hi

normalReserves :: (Integer,Integer) -> Bool
normalReserves = both (within (minReserve*precision) (maxReserve*precision))

normalD :: Integer -> Bool
normalD = within (10^17) (8*wad)

sqrtFloor :: Integer -> Integer
sqrtFloor x
  | x < 0 = error "negative TwoCrypto square root"
  | x < 2 = x
  | otherwise = go (1 + x `div` 2)
 where
  go guess = let next = (guess+x `div` guess) `div` 2
             in if next >= guess then guess else go next

mulOne :: Integer -> Integer -> Integer
mulOne d g = (wad*d `div` gamma)*g `div` gamma*g `div` (ann `div` 10000)

invariant :: (Integer,Integer) -> Maybe Integer
invariant input@(a,b) = do
  guard (normalReserves input && low*wad `div` high >= 10^14)
  iterateD maxSteps (2*sqrtFloor (high*low))
 where
  high = max a b
  low = min a b
  total = high+low
  iterateD 0 _ = Nothing
  iterateD rounds d = do
    guard (normalD d)
    let k0 = ((4*wad*high `div` d)*low) `div` d
        g = abs (gamma+wad-k0)+1
        m1 = mulOne d g
        m2 = 4*wad*k0 `div` g
    guard (k0>0)
    let derivative = total + total*m2 `div` wad + 2*m1 `div` k0 - m2*d `div` wad
    guard (derivative>0)
    let plus = d*(derivative+total) `div` derivative
        base = d*d `div` derivative
        correction = d*(m1 `div` derivative) `div` wad * abs (wad-k0) `div` k0
        minus = if wad>k0 then base+correction else base-correction
        next = if plus>minus then plus-minus else (minus-plus) `div` 2
    guard (minus>=0 && normalD next)
    if abs (next-d)*10^14 < max (10^16) next
      then do
        guard (both (\x -> within (10^16 `div` 2) (10^20 `div` 2) (x*wad `div` next)) input)
        pure next
      else iterateD (rounds-1) next

sourceDiscriminant :: Integer -> Integer -> Integer
sourceDiscriminant d x = delta1*delta1 + (4*delta0*delta0 `quot` b')*delta0
 where
  a = 10^32
  ag = ann*gamma*gamma
  b = d*ag `quot` 400000000 `quot` x - 3*a - 2*gamma*10^14
  c = 3*a+4*gamma*10^14+gamma*gamma `quot` 10^4
      +(4*ag `quot` 400000000)*x `quot` d - 4*ag `quot` 400000000
  dd = negate ((wad+gamma)^ (2::Int) `quot` 10^4)
  deltas aa bb cc dd' = (d0,3*d0+bb - ((27*aa*aa `quot` bb)*dd' `quot` bb))
   where d0 = 3*aa*cc `quot` bb-bb
  (raw0,raw1) = deltas a b c dd
  threshold = minimum [abs raw0,abs raw1,a]
  divider = head ([10^p | (t,p)<-[(48,30),(46,28),(44,26),(42,24),(40,22),(38,20),(36,18),
                (34,16),(32,14),(30,12),(28,10),(26,8),(24,6),(20,2)], threshold>10^t] ++ [1])
  b' = b `quot` divider
  (delta0,delta1) = deltas (a `quot` divider) b' (c `quot` divider) (dd `quot` divider)

fallbackY :: Integer -> Integer -> Maybe Integer
fallbackY d x = do
  guard (normalD d && within (minReserve*precision) (maxReserve*precision) x)
  guard (45*d <= 100*x && 100*x <= 55*d && sourceDiscriminant d x < 0)
  iterateY maxSteps (d*d `div` (4*x))
 where
  k0i = 2*wad*x `div` d
  limit = max 100 (max (x `div` 10^14) (d `div` 10^14))
  iterateY 0 _ = Nothing
  iterateY rounds y = do
    guard (y>0)
    let k0 = k0i*y*2 `div` d
        total = x+y
        g = abs (gamma+wad-k0)+1
        m1 = mulOne d g
        m2 = wad+2*wad*k0 `div` g
        yf = wad*y+total*m2+m1
        loss = d*m2
    if yf<loss then iterateY (rounds-1) (y `div` 2) else do
      let f = (yf-loss) `div` y
      guard (f>0 && k0>0)
      let base = m1 `div` f
          plus = (yf-loss+wad*d) `div` f + base*wad `div` k0
          minus = base+wad*total `div` f
          next = if plus<minus then y `div` 2 else plus-minus
      if abs (next-y) < max limit (next `div` 10^14) then pure next else iterateY (rounds-1) next

dynamicFee :: (Integer,Integer) -> Integer
dynamicFee (a,b) = (midFee*weight + outFee*(wad-weight)) `div` wad
 where
  total = a+b
  balance = (4*wad*a `div` total)*b `div` total
  numerator = feeGamma*balance
  weight = numerator `div` (numerator `div` wad + wad - balance)

spotBound :: (Integer,Integer) -> Integer -> Bool
spotBound (a,b) d = within (95*wad `div` 100) (102*wad `div` 100-1)
  (((4*a*b `div` d)*wad) `div` d)

tweak :: Pool -> (Integer,Integer) -> Integer -> Integer -> Integer -> Maybe Pool
tweak old balances d newSupply credit = do
  guard (newSupply>0 && spotBound (normalized balances) d)
  let nextPrice = wad*(d `div` 2) `div` newSupply + 1
      nextProfit = profit old * nextPrice `div` virtualPrice old
  guard (virtualPrice old < nextPrice && nextPrice <= 2*wad && within wad (4*wad) nextProfit)
  pure old {reserves=balances, storedD=d, supply=newSupply, virtualPrice=nextPrice,
            profit=nextProfit, adminCredit=credit}

join :: Pool -> (Integer,Integer) -> Maybe (Pool,Integer,Integer)
join old amounts = do
  guard (both (>=0) amounts && sumPair amounts>0)
  let balances = zipPair (+) (reserves old) amounts
      xp = normalized balances
  d <- invariant xp
  if supply old==0 then do
    let minted = d `div` 2
    pure (empty {reserves=balances, storedD=d, supply=minted, adminCredit=adminCredit old},minted,0)
  else do
    let gross = supply old*d `div` storedD old - supply old
        average = sumPair amounts `div` 2
        -- The precision factor is even. Compute the exact scaled deviations
        -- before canceling it from their ratio.
        scaled = normalized amounts
        normalizedAverage = sumPair scaled `div` 2
        difference = sumPair (mapPair (abs . subtract normalizedAverage) scaled)
        tokenFeeRate = (dynamicFee xp `div` 2)*difference `div` sumPair scaled + 10^5
        fee = tokenFeeRate*gross `div` feeBase + 1
        minted = gross-fee
    guard (average>=0 && minted>0)
    next <- tweak old balances d (supply old+minted) (adminCredit old+fee `div` 2)
    pure (next,minted,fee)

swap :: Pool -> Int -> Integer -> Maybe (Pool,Integer,Integer)
swap old direction amount = do
  guard (supply old>0 && amount>0 && direction `elem` [0,1])
  let (a,b) = reserves old
      (other,target) = if direction==0 then (a+amount,b) else (b+amount,a)
      x = other*precision
  y <- fallbackY (storedD old) x
  let xp = if direction==0 then (x,y) else (y,x)
      gross = (target*precision-y-1) `div` precision
      fee = dynamicFee xp*gross `div` feeBase
      output = gross-fee
      balances = if direction==0 then (other,target-output) else (target-output,other)
  guard (gross>0 && output>0)
  d <- invariant (normalized balances)
  next <- tweak old balances d (supply old) (adminCredit old)
  pure (next,output,fee)

exit :: Pool -> Integer -> Maybe (Pool,(Integer,Integer))
exit old burned = do
  guard (burned>0 && burned<=supply old)
  let full = burned==supply old
      adjusted = if full then burned else burned-1
      payments = mapPair (\x -> x*adjusted `div` supply old) (reserves old)
      remaining = zipPair (-) (reserves old) payments
      nextD = storedD old - storedD old*adjusted `div` supply old
  guard (full || (normalReserves (normalized remaining) && normalD nextD))
  pure (old {reserves=remaining, storedD=nextD, supply=supply old-burned},payments)

sweep :: Pool -> Maybe (Pool,(Integer,Integer))
sweep old = do
  guard (profit old>profitAnchor old && supply old>=wad)
  let fee = (profit old-profitAnchor old) `div` 4
      fraction = virtualPrice old*wad `div` (virtualPrice old-fee) - wad
      share = adminCredit old + supply old*fraction `div` wad
      newProfit = profit old - fee*2
      including = supply old+share
      nextPrice = wad*(storedD old `div` 2) `div` including
      nextD = storedD old - storedD old*share `div` including
      payments = mapPair (\x -> x*share `div` including) (reserves old)
      remaining = zipPair (-) (reserves old) payments
  guard (fee>0 && share>0 && sumPair payments>0 && within wad (2*wad) nextPrice
         && normalReserves (normalized remaining) && normalD nextD)
  pure (old {reserves=remaining, storedD=nextD, virtualPrice=nextPrice, profit=newProfit,
             profitAnchor=max (profitAnchor old) newProfit, adminCredit=0},payments)

referenceAudit :: Bool
referenceAudit = and
  [ invariant (wad,wad)==Just (2*wad)
  , fallbackY (2*wad) wad==Just wad
  , fallbackY (2*wad) (89*wad `div` 100)==Nothing
  , fallbackY (2*wad) (111*wad `div` 100)==Nothing
  , dynamicFee (wad,wad)==midFee
  , sourceDiscriminant (2*wad) wad<0
  , case join empty (1000000,1000000) of
      Just (p,m,0) -> m==wad && checkSwaps p
      _ -> False
  ]
 where
  checkSwaps p = case (swap p 0 10000,swap p 1 10000) of
    (Just (q,a,f),Just (r,b,g)) ->
      a==b && f==g && f>0 && a>0 && fst (reserves q)==snd (reserves r)
      && virtualPrice q>wad && case sweep q of
        Just (_,fees) -> sumPair fees>0
        Nothing -> False
    _ -> False
