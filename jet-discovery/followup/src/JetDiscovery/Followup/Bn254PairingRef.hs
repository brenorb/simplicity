-- | Integer reference for the EIP-197 BN254 pairing check.
--
-- Tower: Fp2 = Fp[i]/(i^2 + 1); Fp6 = Fp2[v]/(v^3 - xi), xi = 9 + i;
-- Fp12 = Fp6[w]/(w^2 - v).  The twist is y^2 = x^3 + 3/xi and the untwist is
-- (x, y) -> (x w^2, y w^3).  The Miller loop is the binary optimal-ate loop over
-- 6u+2 with affine steps; each step's slope comes with the inverse of its
-- denominator, which the Simplicity verifier checks instead of inverting.
--
-- The final exponentiation is computed two ways: directly as f^((p^12-1)/r),
-- and with the Devegili-Scott-Dahab hard part (three exponentiations by u and
-- Frobenius maps) that the Simplicity program uses.  'selfCheck' confirms that
-- the two agree.
module JetDiscovery.Followup.Bn254PairingRef
  ( p, r, u, F2, F6, F12, Pt2
  , f2mul, f2add, f2sub, f2neg, f2conj, f2inv, f2sq, f2mulXi
  , f6mul, f12mul, f12sq, f12inv, f12one, f12conj, frob, frob2, f12pow, f12mulLine
  , xiPowers, gamma, twistB, g2OnCurve, g2InSubgroup, frobTwist, frob2Twist
  , Step(..), millerSteps, millerLoop, finalExpDirect, finalExpHard, pairingCheck
  , subgroupSteps, loopBits, rMinus1Bits, selfCheck, decodeG1, decodeG2
  ) where

import Data.Bits (testBit, shiftR)

p, r, u :: Integer
p = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
u = 4965661367192848881

md :: Integer -> Integer
md x = x `mod` p

inv1 :: Integer -> Integer
inv1 a = pw a (p - 2) where
  pw _ 0 = 1
  pw b e = let h = pw (b * b `mod` p) (e `div` 2) in if odd e then h * b `mod` p else h

type F2 = (Integer, Integer)              -- a0 + a1 i
type F6 = (F2, F2, F2)                    -- b0 + b1 v + b2 v^2
type F12 = (F6, F6)                       -- c0 + c1 w

f2add, f2sub, f2mul :: F2 -> F2 -> F2
f2add (a, b) (c, d) = (md (a + c), md (b + d))
f2sub (a, b) (c, d) = (md (a - c), md (b - d))
f2mul (a, b) (c, d) = (md (a * c - b * d), md (a * d + b * c))
f2neg, f2conj, f2inv, f2sq, f2mulXi :: F2 -> F2
f2neg (a, b) = (md (-a), md (-b))
f2conj (a, b) = (a, md (-b))
f2inv (a, b) = let t = inv1 (md (a * a + b * b)) in (md (a * t), md (-b * t))
f2sq x = f2mul x x
f2mulXi (a, b) = (md (9 * a - b), md (a + 9 * b))      -- (9 + i)(a + b i)

f2zero, f2one :: F2
f2zero = (0, 0)
f2one = (1, 0)

f6add, f6sub, f6mul :: F6 -> F6 -> F6
f6add (a, b, c) (d, e, f) = (f2add a d, f2add b e, f2add c f)
f6sub (a, b, c) (d, e, f) = (f2sub a d, f2sub b e, f2sub c f)
f6mul (a0, a1, a2) (b0, b1, b2) = (c0, c1, c2)
 where
  m x y = f2mul x y
  c0 = f2add (m a0 b0) (f2mulXi (f2add (m a1 b2) (m a2 b1)))
  c1 = f2add (f2add (m a0 b1) (m a1 b0)) (f2mulXi (m a2 b2))
  c2 = f2add (f2add (m a0 b2) (m a1 b1)) (m a2 b0)
f6neg :: F6 -> F6
f6neg (a, b, c) = (f2neg a, f2neg b, f2neg c)
-- | multiply by v: (b0, b1, b2) -> (xi b2, b0, b1)
f6mulV :: F6 -> F6
f6mulV (a, b, c) = (f2mulXi c, a, b)
f6zero, f6one :: F6
f6zero = (f2zero, f2zero, f2zero)
f6one = (f2one, f2zero, f2zero)
f6inv :: F6 -> F6
f6inv (a0, a1, a2) = (f2mul c0 t, f2mul c1 t, f2mul c2 t)
 where
  c0 = f2sub (f2sq a0) (f2mulXi (f2mul a1 a2))
  c1 = f2sub (f2mulXi (f2sq a2)) (f2mul a0 a1)
  c2 = f2sub (f2sq a1) (f2mul a0 a2)
  t = f2inv (f2add (f2mul a0 c0) (f2mulXi (f2add (f2mul a2 c1) (f2mul a1 c2))))

f12mul :: F12 -> F12 -> F12
f12mul (a0, a1) (b0, b1) = (f6add t0 (f6mulV t1), f6sub (f6sub (f6mul (f6add a0 a1) (f6add b0 b1)) t0) t1)
 where t0 = f6mul a0 b0; t1 = f6mul a1 b1
f12sq :: F12 -> F12
f12sq x = f12mul x x
f12one :: F12
f12one = (f6one, f6zero)
f12conj :: F12 -> F12
f12conj (a, b) = (a, f6neg b)
f12inv :: F12 -> F12
f12inv (a, b) = (f6mul a t, f6neg (f6mul b t))
 where t = f6inv (f6sub (f6mul a a) (f6mulV (f6mul b b)))
f12pow :: F12 -> Integer -> F12
f12pow x e = foldl (\acc i -> let s = f12sq acc in if testBit e i then f12mul s x else s) f12one [nb - 1, nb - 2 .. 0]
 where nb = length (takeWhile (> 0) (iterate (`shiftR` 1) e))

-- | xi^((p-1) k / 6) for k = 0..5, the Frobenius coefficients of w^k.
gamma :: Int -> F2
gamma k = f2pow (9, 1) (toInteger k * (p - 1) `div` 6)
f2pow :: F2 -> Integer -> F2
f2pow x e = foldl (\acc i -> let s = f2sq acc in if testBit e i then f2mul s x else s) f2one [nb - 1, nb - 2 .. 0]
 where nb = length (takeWhile (> 0) (iterate (`shiftR` 1) e))
xiPowers :: [F2]
xiPowers = map gamma [0 .. 5]

-- | Frobenius x -> x^p: conj each coefficient of w^k and multiply by gamma k.
-- Coefficients of w^0..w^5 are b0, b0', b1, b1', b2, b2' for f = (b0,b1,b2) + (b0',b1',b2') w.
frob :: F12 -> F12
frob ((a0, a1, a2), (b0, b1, b2)) =
  ( (f2conj a0, f2mul (f2conj a1) (gamma 2), f2mul (f2conj a2) (gamma 4))
  , (f2mul (f2conj b0) (gamma 1), f2mul (f2conj b1) (gamma 3), f2mul (f2conj b2) (gamma 5)) )
frob2 :: F12 -> F12
frob2 = frob . frob

-- Twist ---------------------------------------------------------------------------

type Pt2 = (F2, F2)

twistB :: F2
twistB = f2mul (3, 0) (f2inv (9, 1))

g2OnCurve :: Pt2 -> Bool
g2OnCurve (x, y) = f2sq y == f2add (f2mul (f2sq x) x) twistB

-- | pi on the twist: (conj x * gamma 2, conj y * gamma 3).
frobTwist :: Pt2 -> Pt2
frobTwist (x, y) = (f2mul (f2conj x) (gamma 2), f2mul (f2conj y) (gamma 3))
frob2Twist :: Pt2 -> Pt2
frob2Twist = frobTwist . frobTwist

-- | One affine step: the slope's numerator, denominator and the denominator's
-- inverse (the witness hint), and the resulting point.
data Step = Step { stNum :: F2, stDen :: F2, stInv :: F2, stLambda :: F2, stIn :: Pt2, stOut :: Pt2 }
  deriving Show

dblStep :: Pt2 -> Step
dblStep t@(x, y) = mk t (f2mul (3, 0) (f2sq x)) (f2add y y) (\l -> let x' = f2sub (f2sq l) (f2add x x) in (x', f2sub (f2mul l (f2sub x x')) y))
addStep :: Pt2 -> Pt2 -> Step
addStep t@(x1, y1) (x2, y2) = mk t (f2sub y2 y1) (f2sub x2 x1) (\l -> let x' = f2sub (f2sub (f2sq l) x1) x2 in (x', f2sub (f2mul l (f2sub x1 x')) y1))
mk :: Pt2 -> F2 -> F2 -> (F2 -> Pt2) -> Step
mk t num den next = Step num den i l t (next l)
 where i = if den == f2zero then f2zero else f2inv den
       l = f2mul num i

-- | Bits of 6u+2 after the leading one, most significant first.
loopBits :: [Bool]
loopBits = tail [ testBit e i | i <- [nb - 1, nb - 2 .. 0] ]
 where e = 6 * u + 2; nb = length (takeWhile (> 0) (iterate (`shiftR` 1) e))

-- | The steps of one pair's Miller loop: per loop bit a doubling and maybe an
-- addition, then the two Frobenius additions (the last one does not move T).
millerSteps :: Pt2 -> [Step]
millerSteps q = go q loopBits
 where
  go t [] = let s1 = addStep t (frobTwist q)
                (x2, y2) = frob2Twist q
                s2 = addStep (stOut s1) (x2, f2neg y2)
            in [s1, s2]
  go t (b:bs) = let d = dblStep t
                    t' = stOut d
                in if b then let a = addStep t' q in d : a : go (stOut a) bs else d : go t' bs

-- | Line through the step's input point with its slope, evaluated at P:
-- l = yP - lambda xP w + (lambda x_T - y_T) w^3.
f12mulLine :: F12 -> (Integer, Integer) -> Step -> F12
f12mulLine f (xp, yp) st = f12mul f line
 where
  l = stLambda st
  (xt, yt) = stIn st
  line = (((yp, 0), f2zero, f2zero), (f2neg (f2mul l (xp, 0)), f2sub (f2mul l xt) yt, f2zero))

-- | Miller loop over several pairs sharing the accumulator.
millerLoop :: [((Integer, Integer), Pt2)] -> F12
millerLoop pairs = go f12one (map (millerSteps . snd) pairs) loopBits
 where
  ps = map fst pairs
  go f stss [] = foldl (\acc (pt, [s1, s2]) -> f12mulLine (f12mulLine acc pt s1) pt s2) f (zip ps stss)
  go f stss (b:bs) =
    let f' = foldl (\acc (pt, st:_) -> f12mulLine acc pt st) (f12sq f) (zip ps stss)
        rest1 = map tail stss
        (f'', rest2) = if b then (foldl (\acc (pt, st:_) -> f12mulLine acc pt st) f' (zip ps rest1), map tail rest1) else (f', rest1)
    in go f'' rest2 bs
  go _ _ _ = error "millerLoop"

finalExpDirect :: F12 -> F12
finalExpDirect f = f12pow f ((p ^ (12 :: Int) - 1) `div` r)

-- | Easy part f^((p^6-1)(p^2+1)) then the Devegili-Scott-Dahab hard part.
finalExpHard :: F12 -> F12
finalExpHard f = t0'''
 where
  t1a = f12mul (f12conj f) (f12inv f)
  t1 = f12mul t1a (frob2 t1a)
  fp = frob t1; fp2 = frob2 t1; fp3 = frob fp2
  fu = f12pow t1 u; fu2 = f12pow fu u; fu3 = f12pow fu2 u
  y3 = f12conj (frob fu); fu2p = frob fu2; fu3p = frob fu3; y2 = frob2 fu2
  y0 = f12mul (f12mul fp fp2) fp3
  y1 = f12conj t1
  y5 = f12conj fu2
  y4 = f12conj (f12mul fu fu2p)
  y6 = f12conj (f12mul fu3 fu3p)
  t0 = f12mul (f12mul (f12sq y6) y4) y5
  t1' = f12mul (f12mul y3 y5) t0
  t0' = f12mul t0 y2
  t1'' = f12sq (f12mul (f12sq t1') t0')
  t0'' = f12mul t1'' y1
  t1''' = f12mul t1'' y0
  t0''' = f12mul (f12sq t0'') t1'''

-- G1/G2 decoding and the precompile ------------------------------------------------

decodeG1 :: (Integer, Integer) -> Maybe (Maybe (Integer, Integer))
decodeG1 (x, y)
  | x >= p || y >= p = Nothing
  | x == 0 && y == 0 = Just Nothing
  | md (y * y - x * x * x - 3) == 0 = Just (Just (x, y))
  | otherwise = Nothing

-- | EVM order: x.imag, x.real, y.imag, y.real.
decodeG2 :: (Integer, Integer, Integer, Integer) -> Maybe (Maybe Pt2)
decodeG2 (xi, xr, yi, yr)
  | any (>= p) [xi, xr, yi, yr] = Nothing
  | all (== 0) [xi, xr, yi, yr] = Just Nothing
  | not (g2OnCurve q) = Nothing
  | not (g2InSubgroup q) = Nothing
  | otherwise = Just (Just q)
 where q = ((xr, xi), (yr, yi))

-- | Bits of r-1 after the leading one, most significant first.
rMinus1Bits :: [Bool]
rMinus1Bits = tail [ testBit (r - 1) i | i <- [nb - 1, nb - 2 .. 0] ]
 where nb = length (takeWhile (> 0) (iterate (`shiftR` 1) (r - 1)))

-- | Affine steps computing (r-1) Q; Q is in the subgroup iff the result is -Q
-- and no step has a zero denominator.
subgroupSteps :: Pt2 -> [Step]
subgroupSteps q = go q rMinus1Bits
 where
  go _ [] = []
  go t (b:bs) = let d = dblStep t
                in if b then let a = addStep (stOut d) q in d : a : go (stOut a) bs else d : go (stOut d) bs

g2InSubgroup :: Pt2 -> Bool
g2InSubgroup q@(x, y) = all ((/= f2zero) . stDen) sts && end == (x, f2neg y)
 where sts = subgroupSteps q
       end = if null sts then q else stOut (last sts)

-- | Nothing when the precompile fails; otherwise whether the product is one.
pairingCheck :: [((Integer, Integer), (Integer, Integer, Integer, Integer))] -> Maybe Bool
pairingCheck raw = do
  pts <- mapM (\(a, b) -> (,) <$> decodeG1 a <*> decodeG2 b) raw
  let live = [ (pt, q) | (Just pt, Just q) <- pts ]
  return (null live || finalExpHard (millerLoop live) == f12one)

-- | Internal consistency of the tower, Frobenius and final exponentiation.
selfCheck :: Bool
selfCheck = and
  [ f12mul x (f12inv x) == f12one
  , frob x == f12pow x p
  , frob2 x == f12pow x (p * p)
  , finalExpHard x == finalExpDirect x
  , twistOk ]
 where
  x = (((3, 5), (7, 11), (13, 17)), ((19, 23), (29, 31), (37, 41)))
  twistOk = f2sq (gamma 1) == gamma 2 && f2mul (gamma 2) (gamma 1) == gamma 3
