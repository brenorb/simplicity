{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
-- | Exact EIP-197 BN254 pairing-check relation (precompile 0x08) for k pairs.
--
-- The program checks a claimed 32-byte output (0 or 1) against k (G1, G2)
-- inputs with the precompile's rules (go-ethereum gnark backend):
--
-- * G1: coordinates below p; (0,0) is infinity; otherwise on y^2 = x^3 + 3.
-- * G2: EVM order (x.im, x.re, y.im, y.re), each below p; all-zero is
--   infinity; otherwise on the twist y^2 = x^3 + 3/(9+i) and in the order-r
--   subgroup.
-- * Output 1 iff the product of pairings is one; pairs with an infinity
--   factor contribute one.
--
-- Arithmetic is the Montgomery field of "JetDiscovery.Followup.Bn254Precompiles"
-- with the tower of "JetDiscovery.Followup.Bn254PairingRef".  Every affine
-- step (Miller loop over 6u+2 and the subgroup check (r-1)Q = -Q) takes the
-- inverse of its slope denominator as a witness hint and checks den * inv = 1,
-- so a zero denominator rejects.  The easy part of the final exponentiation
-- takes the Fp12 inverse as a hint, checked by multiplication; the hard part
-- is the Devegili-Scott-Dahab chain (three exponentiations by u).
--
-- Each pair runs its own Miller loop and the k results are multiplied before
-- one final exponentiation: k-1 more sets of 64 Fp12 squarings than a shared
-- accumulator, in exchange for one pair builder shared by every k.  Lines are
-- multiplied as dense Fp12 elements (no sparse multiplication).  Both choices
-- overstate the cost of an optimised verifier.
module JetDiscovery.Followup.Bn254Pairing
  ( F2, F6, F12, PairHints(..), PairingW, pairingT, pairingHints
  , f2mulT, f6mulT, f12mulT, f12sqT, frobT, powUT, conj12T, one12, monty, montyF12, montyF2
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Prelude as P
import Data.Bits (testBit, shiftR)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Ty.Word
import JetDiscovery.Followup.Bn254Precompiles
  (Fp, Aff, montMul, toM, kw, oneM, add2, sub2, mul2, dbl, isZero, validPt, pBN)
import qualified JetDiscovery.Followup.Bn254PairingRef as R

type F2 = (Fp, Fp)
type F6 = (F2, (F2, F2))
type F12 = (F6, F6)

-- | Montgomery form of an integer.
monty :: Integer -> Integer
monty x = x * 2 ^ (256 :: Int) `mod` pBN

k2 :: (Core term, TyC a) => R.F2 -> term a F2
k2 (a, b) = kw (monty a) &&& kw (monty b)

z2, one2 :: (Core term, TyC a) => term a F2
z2 = kw 0 &&& kw 0
one2 = kw oneM &&& kw 0

-- Fp2 ---------------------------------------------------------------------------

f2addT, f2subT, f2mulT :: Core term => term (F2, F2) F2
f2addT = add2 ooh ioh &&& add2 oih iih
f2subT = sub2 ooh ioh &&& sub2 oih iih
-- | Karatsuba: (a0 b0 - a1 b1, (a0 + a1)(b0 + b1) - a0 b0 - a1 b1).
f2mulT = (iden &&& (mul2 ooh ioh &&& mul2 oih iih)) >>> (sub2 t0 t1 &&& sub2 (sub2 (mul2 (add2 a0 a1) (add2 b0 b1)) t0) t1)
 where
  t0 = ih >>> oh
  t1 = ih >>> ih
  a0 = oh >>> ooh
  a1 = oh >>> oih
  b0 = oh >>> ioh
  b1 = oh >>> iih

f2sqT, f2negT, f2conjT, f2mulXiT :: Core term => term F2 F2
f2sqT = mul2 (add2 oh ih) (sub2 oh ih) &&& dbl (mul2 oh ih)
f2negT = sub2 (kw 0) oh &&& sub2 (kw 0) ih
f2conjT = oh &&& sub2 (kw 0) ih
-- | (9 + i)(a + b i) = (9a - b) + (a + 9b) i
f2mulXiT = sub2 (nine oh) ih &&& add2 oh (nine ih)
 where nine x = add2 (dbl (dbl (dbl x))) x

m2, a2, s2 :: (Core term, TyC s) => term s F2 -> term s F2 -> term s F2
m2 x y = (x &&& y) >>> f2mulT
a2 x y = (x &&& y) >>> f2addT
s2 x y = (x &&& y) >>> f2subT

-- Fp6 = Fp2[v]/(v^3 - xi) -----------------------------------------------------------

f6mulT :: Core term => term (F6, F6) F6
f6mulT = (iden &&& (m2 a0 b0 &&& (m2 a1 b1 &&& m2 a2' b2))) >>> (c0 &&& (c1 &&& c2))
 where
  a0 = ooh
  a1 = oih >>> oh
  a2' = oih >>> ih
  b0 = ioh
  b1 = iih >>> oh
  b2 = iih >>> ih
  e = oh
  w0 = ih >>> oh
  w1 = ih >>> ih >>> oh
  w2 = ih >>> ih >>> ih
  cross x y u v = m2 (a2 (e >>> x) (e >>> y)) (a2 (e >>> u) (e >>> v))
  c0 = a2 w0 (s2 (s2 (cross a1 a2' b1 b2) w1) w2 >>> f2mulXiT)
  c1 = a2 (s2 (s2 (cross a0 a1 b0 b1) w0) w1) (w2 >>> f2mulXiT)
  c2 = a2 (s2 (s2 (cross a0 a2' b0 b2) w0) w2) w1

f6addT, f6subT :: Core term => term (F6, F6) F6
f6addT = a2 ooh ioh &&& (a2 (oih >>> oh) (iih >>> oh) &&& a2 (oih >>> ih) (iih >>> ih))
f6subT = s2 ooh ioh &&& (s2 (oih >>> oh) (iih >>> oh) &&& s2 (oih >>> ih) (iih >>> ih))

f6negT, f6mulVT :: Core term => term F6 F6
f6negT = (oh >>> f2negT) &&& ((ih >>> oh >>> f2negT) &&& (ih >>> ih >>> f2negT))
-- | v (b0 + b1 v + b2 v^2) = xi b2 + b0 v + b1 v^2
f6mulVT = (ih >>> ih >>> f2mulXiT) &&& (oh &&& (ih >>> oh))

m6, a6, s6 :: (Core term, TyC s) => term s F6 -> term s F6 -> term s F6
m6 x y = (x &&& y) >>> f6mulT
a6 x y = (x &&& y) >>> f6addT
s6 x y = (x &&& y) >>> f6subT

-- Fp12 = Fp6[w]/(w^2 - v) -----------------------------------------------------------

f12mulT :: Core term => term (F12, F12) F12
f12mulT = (iden &&& (m6 ooh ioh &&& m6 oih iih)) >>>
          (a6 t0 (t1 >>> f6mulVT) &&& s6 (s6 (m6 (a6 (oh >>> ooh) (oh >>> oih)) (a6 (oh >>> ioh) (oh >>> iih))) t0) t1)
 where
  t0 = ih >>> oh
  t1 = ih >>> ih

-- | (a0 + a1 w)^2 = ((a0 + a1)(a0 + v a1) - t - v t) + 2t w with t = a0 a1.
f12sqT :: Core term => term F12 F12
f12sqT = (iden &&& m6 oh ih) >>>
         (s6 (s6 (m6 (a6 (oh >>> oh) (oh >>> ih)) (a6 (oh >>> oh) (oh >>> ih >>> f6mulVT))) ih) (ih >>> f6mulVT) &&& a6 ih ih)

conj12T :: Core term => term F12 F12
conj12T = oh &&& (ih >>> f6negT)

one12 :: (Core term, TyC a) => term a F12
one12 = (one2 &&& (z2 &&& z2)) &&& (z2 &&& (z2 &&& z2))

m12 :: (Core term, TyC s) => term s F12 -> term s F12 -> term s F12
m12 x y = (x &&& y) >>> f12mulT

-- | x -> x^p: conjugate the coefficient of w^k and multiply by xi^((p-1)k/6).
frobT :: Core term => term F12 F12
frobT = ((ooh >>> f2conjT) &&& (g (oih >>> oh) 2 &&& g (oih >>> ih) 4)) &&& (g ioh 1 &&& (g (iih >>> oh) 3 &&& g (iih >>> ih) 5))
 where g x k = m2 (x >>> f2conjT) (k2 (R.gamma k))

frob2T :: Core term => term F12 F12
frob2T = frobT >>> frobT

bitsMsbFirst :: Integer -> [Bool]
bitsMsbFirst e = [ testBit e i | i <- [nb - 1, nb - 2 .. 0] ]
 where nb = length (takeWhile (> 0) (iterate (`shiftR` 1) e))

-- | x -> x^u by square and multiply over the bits of u.
powUT :: Core term => term F12 F12
powUT = (iden &&& iden) >>> P.foldl (>>>) iden (map step (P.drop 1 (bitsMsbFirst R.u))) >>> ih
 where step b = (oh &&& (ih >>> f12sqT)) >>> (if b then oh &&& ((ih &&& oh) >>> f12mulT) else iden)

-- | Inverse from a witness hint g, checked as f g = 1.
inv12T :: (Assert term, Witness term) => F12 -> term F12 F12
inv12T g = (iden &&& witness g) >>> ((f12mulT &&& one12) >>> eq >>> verify) &&& ih >>> ih

-- | f^((p^12-1)/r): easy part with a hinted inverse, then the hard part.
finalExpT :: forall term. (Assert term, Witness term) => F12 -> term F12 F12
finalExpT g = easy >>> s1 >>> s2 >>> s3 >>> s4 >>> s5 >>> s6' >>> s7 >>> res
 where
  easy = ((conj12T &&& inv12T g) >>> f12mulT) >>> (iden &&& frob2T) >>> f12mulT
  -- E1 = (t1, fu); E2 = (E1, fu2); E3 = (E2, fu3)
  s1 = iden &&& powUT
  s2 = iden &&& (ih >>> powUT)
  s3 = iden &&& (ih >>> powUT)
  t1 = oh >>> oh >>> oh
  fu = oh >>> oh >>> ih
  fu2 = oh >>> ih
  fu3 = ih
  -- E4 = (E3, (y0, (y1, (y2, (y3, (y4, (y5, y6)))))))
  y0e = m12 (m12 (t1 >>> frobT) (t1 >>> frob2T)) (t1 >>> frob2T >>> frobT)
  y4e = m12 fu (fu2 >>> frobT) >>> conj12T
  y6e = m12 fu3 (fu3 >>> frobT) >>> conj12T
  s4 = iden &&& (y0e &&& ((t1 >>> conj12T) &&& ((fu2 >>> frob2T) &&& ((fu >>> frobT >>> conj12T) &&& (y4e &&& ((fu2 >>> conj12T) &&& y6e))))))
  -- selectors on E4
  y0 = ih >>> oh
  y1 = ih >>> ih >>> oh
  y2 = ih >>> ih >>> ih >>> oh
  y3 = ih >>> ih >>> ih >>> ih >>> oh
  y4 = ih >>> ih >>> ih >>> ih >>> ih >>> oh
  y5 = ih >>> ih >>> ih >>> ih >>> ih >>> ih >>> oh
  y6 = ih >>> ih >>> ih >>> ih >>> ih >>> ih >>> ih
  -- E5 = (E4, t0), t0 = y6^2 y4 y5
  s5 = iden &&& m12 (m12 (y6 >>> f12sqT) y4) y5
  -- E6 = (E5, (t1', t0')), t1' = y3 y5 t0, t0' = t0 y2
  s6' = iden &&& (m12 (m12 (oh >>> y3) (oh >>> y5)) ih &&& m12 ih (oh >>> y2))
  -- E7 = (E6, t1''), t1'' = (t1'^2 t0')^2
  s7 = iden &&& (m12 (ih >>> oh >>> f12sqT) (ih >>> ih) >>> f12sqT)
  e4of7 = oh >>> oh >>> oh
  res = m12 (m12 ih (e4of7 >>> y1) >>> f12sqT) (m12 ih (e4of7 >>> y0))

-- Affine steps with hinted inverses ---------------------------------------------------

type Pt2 = (F2, F2)

-- | Slope num/den from a hinted inverse h (checked den * h = 1).
slope :: (Assert term, Witness term, TyC s) => term s F2 -> term s F2 -> F2 -> term s F2
slope num den h = (iden &&& witness h) >>> (((m2 (oh >>> den) ih &&& one2) >>> eq >>> verify) &&& m2 (oh >>> num) ih) >>> ih

-- | Given T, the other point B (or T itself for doubling) and the slope, the new point.
nextPt :: (Core term, TyC s) => term s Pt2 -> term s Pt2 -> term s F2 -> term s Pt2
nextPt t b l = (iden &&& s2 (s2 (l >>> f2sqT) (t >>> oh)) (b >>> oh)) >>> (ih &&& s2 (m2 (oh >>> l) (s2 (oh >>> t >>> oh) ih)) (oh >>> t >>> ih))

-- | Line through T with slope l, at P: yP - l xP w + (l xT - yT) w^3.
lineT :: (Core term, TyC s) => term s Aff -> term s Pt2 -> term s F2 -> term s F12
lineT pt t l = c0 &&& c1
 where
  c0 = ((pt >>> ih) &&& kw 0) &&& (z2 &&& z2)
  lxP = (mul2 (l >>> oh) (pt >>> oh) &&& mul2 (l >>> ih) (pt >>> oh)) >>> f2negT
  c1 = lxP &&& (s2 (m2 l (t >>> oh)) (t >>> ih) &&& z2)

-- | Hints of one pair: the subgroup-check and Miller-loop inverses (Montgomery form).
data PairHints = PairHints { phSubgroup :: [F2], phMiller :: [F2] }

-- | (r-1)Q = -Q with every step's denominator inverted by a hint.
subgroupT :: forall term. (Assert term, Witness term) => [F2] -> term Pt2 ()
subgroupT hs = (iden &&& iden) >>> P.foldl (>>>) iden steps >>> ((ih &&& (oh >>> (oh &&& (ih >>> f2negT)))) >>> eq >>> verify)
 where
  -- state (Q, T)
  q = oh
  t = ih
  kinds = concat [ if b then [False, True] else [False] | b <- R.rMinus1Bits ]
  steps = zipWith step kinds (hs ++ repeat (toWord256 0, toWord256 0))
  step False h = oh &&& ((iden &&& slope (m2 (k2 (3, 0)) (t >>> oh >>> f2sqT)) (dblY t) h) >>> nextPt (oh >>> t) (oh >>> t) ih)
  step True h = oh &&& ((iden &&& slope (s2 (q >>> ih) (t >>> ih)) (s2 (q >>> oh) (t >>> oh)) h) >>> nextPt (oh >>> t) (oh >>> q) ih)
  dblY x = a2 (x >>> ih) (x >>> ih)

-- | Miller loop of one pair: input (P, Q) in Montgomery form, output f.
millerT :: forall term. (Assert term, Witness term) => [F2] -> term (Aff, Pt2) F12
millerT hs = (iden &&& (q1 &&& mq2)) >>> (iden &&& (one12 &&& (oh >>> ih))) >>> P.foldl (>>>) iden steps >>> (ih >>> oh)
 where
  frobTw = m2 (oh >>> f2conjT) (k2 (R.gamma 2)) &&& m2 (ih >>> f2conjT) (k2 (R.gamma 3))
  q1 = ih >>> frobTw
  mq2 = ih >>> frobTw >>> frobTw >>> (oh &&& (ih >>> f2negT))
  -- state S = ((E, (Q1, -Q2)), (f, T)), E = (P, Q)
  pt = oh >>> oh >>> oh
  qQ = oh >>> oh >>> ih
  qQ1 = oh >>> ih >>> oh
  qMQ2 = oh >>> ih >>> ih
  ff = ih >>> oh
  tT = ih >>> ih
  kinds = concat [ if b then [Nothing, Just qQ] else [Nothing] | b <- R.loopBits ] ++ [Just qQ1, Just qMQ2]
  steps = zipWith step kinds (hs ++ repeat (toWord256 0, toWord256 0))
  -- in X = (S, slope)
  step Nothing h = (iden &&& slope (m2 (k2 (3, 0)) (tT >>> oh >>> f2sqT)) (a2 (tT >>> ih) (tT >>> ih)) h) >>>
                   ((oh >>> oh) &&& ((((oh >>> ff >>> f12sqT) &&& lineT (oh >>> pt) (oh >>> tT) ih) >>> f12mulT) &&& nextPt (oh >>> tT) (oh >>> tT) ih))
  step (Just b) h = (iden &&& slope (s2 (b >>> ih) (tT >>> ih)) (s2 (b >>> oh) (tT >>> oh)) h) >>>
                    ((oh >>> oh) &&& (m12 (oh >>> ff) (lineT (oh >>> pt) (oh >>> tT) ih) &&& nextPt (oh >>> tT) (oh >>> b) ih))

-- Pairs and the precompile -----------------------------------------------------------

-- | One pair as given in calldata: ((x, y), (x.im, x.re, y.im, y.re)), plain integers.
type PairIn = (Aff, ((Fp, Fp), (Fp, Fp)))

ltP :: (Core term, TyC s) => term s Fp -> term s Bit
ltP x = (x &&& kw pBN) >>> Arith.lt word256

pairT :: forall term. (Assert term, Witness term) => PairIn -> PairHints -> term () F12
pairT w hints = witness w >>> (iden &&& qM) >>> body
 where
  -- Y = (PairIn, Q in Montgomery form)
  g1 = oh >>> oh
  xi_ = oh >>> ih >>> ooh
  xr = oh >>> ih >>> oih
  yi = oh >>> ih >>> ioh
  yr = oh >>> ih >>> iih
  qM = ((ih >>> oih >>> toM) &&& (ih >>> ooh >>> toM)) &&& ((ih >>> iih >>> toM) &&& (ih >>> ioh >>> toM))
  g1check = g1 >>> validPt
  g2canon = and (and (ltP xi_) (ltP xr)) (and (ltP yi) (ltP yr)) >>> verify
  g1inf = and (isZero (g1 >>> oh)) (isZero (g1 >>> ih))
  g2inf = and (and (isZero xi_) (isZero xr)) (and (isZero yi) (isZero yr))
  onTwist = ((ih >>> ih >>> f2sqT) &&& a2 (m2 (ih >>> oh >>> f2sqT) (ih >>> oh)) (k2 R.twistB)) >>> eq >>> verify
  g2check = (g2inf &&& iden) >>> cond unit ((onTwist &&& (ih >>> subgroupT (phSubgroup hints))) >>> unit)
  pM = g1 >>> ((oh >>> toM) &&& (ih >>> toM))
  active = or g1inf g2inf >>> not iden
  res = (active &&& iden) >>> cond ((pM &&& ih) >>> millerT (phMiller hints)) one12
  body = (((g1check &&& g2canon) &&& g2check) &&& res) >>> ih

-- | Witness data of one vector: pairs, their hints, the Fp12 inverse hint and the claimed output word.
type PairingW = ([(PairIn, PairHints)], (F12, Word256))

pairingT :: forall term. (Assert term, Witness term) => PairingW -> term () ()
pairingT (pairs, (ginv, out)) = case map (uncurry pairT) pairs of
  [] -> claimedIs true
  t : ts -> claimedIs (P.foldl (\acc x -> (acc &&& x) >>> f12mulT) t ts >>> finalExpT ginv >>> ((iden &&& one12) >>> eq))
 where
  claimed :: term () Word256
  claimed = witness out
  isWord n = (claimed &&& kw n) >>> eq
  claimedIs :: term () Bit -> term () ()
  claimedIs bitT = ((or (isWord 0) (isWord 1) >>> verify) &&& ((bitT &&& isWord 1) >>> eq >>> verify)) >>> unit

-- Witness construction ---------------------------------------------------------------

montyF2 :: R.F2 -> F2
montyF2 (a, b) = (toWord256 (monty a), toWord256 (monty b))

montyF12 :: R.F12 -> F12
montyF12 ((a0, a1, a2'), (b0, b1, b2)) = ((montyF2 a0, (montyF2 a1, montyF2 a2')), (montyF2 b0, (montyF2 b1, montyF2 b2)))

-- | Witness for a list of ((x, y), (x.im, x.re, y.im, y.re)) pairs and a claimed output.
pairingHints :: [((Integer, Integer), (Integer, Integer, Integer, Integer))] -> Integer -> PairingW
pairingHints raw out = (map one raw, (montyF12 ginv, toWord256 out))
 where
  one (g1@(x, y), g2@(a, b, c, d)) = (((toWord256 x, toWord256 y), ((toWord256 a, toWord256 b), (toWord256 c, toWord256 d))), hints g1 g2)
  hints g1 g2 = case (R.decodeG1 g1, R.decodeG2 g2) of
    (Just (Just _), Just (Just q)) -> PairHints (map (montyF2 . R.stInv) (R.subgroupSteps q)) (map (montyF2 . R.stInv) (R.millerSteps q))
    (_, Just (Just q)) -> PairHints (map (montyF2 . R.stInv) (R.subgroupSteps q)) []
    _ -> PairHints [] []
  live = [ (pt, q) | (g1, g2) <- raw, Just (Just pt) <- [R.decodeG1 g1], Just (Just q) <- [R.decodeG2 g2] ]
  f = if null live then R.f12one else R.millerLoop live
  ginv = R.f12inv f
