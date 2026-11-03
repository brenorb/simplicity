{-# LANGUAGE ScopedTypeVariables #-}
-- | Kernels of a Circle STARK verifier (as in StarkWare's Stwo and its
-- OP_CAT-based Bitcoin verifier): arithmetic in the Mersenne-31 field M31,
-- its degree-4 extension QM31, and one circle-FRI folding step.
--
-- A whole verifier is far beyond one program here; reports/ combines these
-- measured kernel costs with operation counts into an ESTIMATE.
module JetDiscovery.Corpus.Stark
  ( entries
  , m31Mul, qm31Mul, friFold
  , hMul, hQMul, p31, toQ, hFold, hQAdd, hQSub
  , m31Add, m31Sub, m31Fix, qm31Add, qm31Sub, qm31MulBase
  , HQ, QM31, M31
  ) where

import Prelude hiding (drop, take, not, and, or, subtract)
import qualified Data.ByteString as BS

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.Word as Word
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes (konst, w8, w32)
import JetDiscovery.Tx
import JetDiscovery.Types

p31 :: Integer
p31 = 2 ^ (31 :: Int) - 1

type M31 = Word32
type CM31 = (M31, M31)
type QM31 = (CM31, CM31)

kp :: (Core term, TyC i) => term i Word32
kp = konst (w32 p31)

-- | x < p after: if x >= p then x - p else x.
m31Fix :: Assert term => term Word32 Word32
m31Fix = iden &&& (iden &&& kp >>> Arith.subtract word32) >>> (ioh &&& (oh &&& iih)) >>> cond oh ih

m31Add :: Assert term => term (M31, M31) M31
m31Add = Arith.add word32 >>> ih >>> m31Fix

m31Sub :: Assert term => term (M31, M31) M31
m31Sub = Arith.subtract word32 >>> cond (iden &&& kp >>> Arith.add word32 >>> ih) iden

-- | Multiply and reduce: x = a*b < 2^62; x = q 2^31 + r, x == q + r (mod p).
m31Mul :: Assert term => term (M31, M31) M31
m31Mul = Arith.multiply word32 >>> reduce
 where
  -- input (hi, lo) of the 64-bit product
  r = drop (iden &&& kp >>> Word.bitwise_and word32)
  q = (take (konst (w8 1) &&& iden >>> Word.left_shift word8 word32) &&& drop (konst (w8 31) &&& iden >>> Word.right_shift word8 word32))
      >>> Word.bitwise_or word32
  reduce = q &&& r >>> Arith.add word32 >>> ih >>> fold1 >>> m31Fix
  -- t = (s & p) + (s >> 31) maps any 32-bit s to at most p + 1
  fold1 = (iden &&& kp >>> Word.bitwise_and word32) &&& (konst (w8 31) &&& iden >>> Word.right_shift word8 word32) >>> Arith.add word32 >>> ih

-- CM31 = M31[i]/(i^2 + 1)
cm31Add, cm31Sub, cm31Mul :: Assert term => term (CM31, CM31) CM31
cm31Add = (ooh &&& ioh >>> m31Add) &&& (oih &&& iih >>> m31Add)
cm31Sub = (ooh &&& ioh >>> m31Sub) &&& (oih &&& iih >>> m31Sub)
cm31Mul = (((ooh &&& ioh >>> m31Mul) &&& (oih &&& iih >>> m31Mul)) >>> m31Sub)
      &&& (((ooh &&& iih >>> m31Mul) &&& (oih &&& ioh >>> m31Mul)) >>> m31Add)

-- | Multiply by u^2 = 2 + i: (a + bi)(2 + i) = (2a - b) + (a + 2b) i.
cm31MulR :: Assert term => term CM31 CM31
cm31MulR = (((oh &&& oh >>> m31Add) &&& ih) >>> m31Sub) &&& (oh &&& (ih &&& ih >>> m31Add) >>> m31Add)

-- QM31 = CM31[u]/(u^2 - (2 + i))
qm31Add, qm31Sub, qm31Mul :: Assert term => term (QM31, QM31) QM31
qm31Add = (ooh &&& ioh >>> cm31Add) &&& (oih &&& iih >>> cm31Add)
qm31Sub = (ooh &&& ioh >>> cm31Sub) &&& (oih &&& iih >>> cm31Sub)
qm31Mul = (((ooh &&& ioh >>> cm31Mul) &&& ((oih &&& iih >>> cm31Mul) >>> cm31MulR)) >>> cm31Add)
      &&& (((ooh &&& iih >>> cm31Mul) &&& (oih &&& ioh >>> cm31Mul)) >>> cm31Add)

-- | QM31 times an M31 scalar.
qm31MulBase :: Assert term => term (QM31, M31) QM31
qm31MulBase = ((take ooh &&& ih >>> m31Mul) &&& (take oih &&& ih >>> m31Mul)) &&& ((take ioh &&& ih >>> m31Mul) &&& (take iih &&& ih >>> m31Mul))

-- | Circle FRI line folding (Stwo's fold_line): given f(x), f(-x), 1/x and alpha:
-- f0 = f(x) + f(-x); f1 = (f(x) - f(-x)) / x; result = f0 + alpha f1.
friFold :: Assert term => term ((QM31, QM31), (M31, QM31)) QM31
friFold = (take qm31Add &&& ((iih &&& ((take qm31Sub &&& ioh) >>> qm31MulBase)) >>> qm31Mul)) >>> qm31Add

-- | a^(p-2) with an explicit accumulator: input a, output a^(p-2).
m31Pow :: Assert term => term M31 M31
m31Pow = iden &&& konst (w32 1) >>> foldr (\b k -> stepB b >>> k) ih bits
 where
  bits = [ ((p31 - 2) `div` 2 ^ i) `mod` 2 == 1 | i <- [30, 29 .. 0 :: Int] ]
  -- state (a, acc): acc = acc^2, then acc = acc * a if the bit is set
  stepB b = oh &&& (drop (iden &&& iden >>> m31Mul)) >>> (if b then oh &&& (ih &&& oh >>> m31Mul) else iden)

-- Haskell reference ---------------------------------------------------------------

type HQ = ((Integer, Integer), (Integer, Integer))

hMul :: Integer -> Integer -> Integer
hMul a b = a * b `mod` p31

hCMul :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer)
hCMul (a, b) (c, d) = ((a * c - b * d) `mod` p31, (a * d + b * c) `mod` p31)

hCAdd, hCSub :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer)
hCAdd (a, b) (c, d) = ((a + c) `mod` p31, (b + d) `mod` p31)
hCSub (a, b) (c, d) = ((a - c) `mod` p31, (b - d) `mod` p31)

hQMul :: HQ -> HQ -> HQ
hQMul (x0, x1) (y0, y1) = (hCAdd (hCMul x0 y0) (hCMul (hCMul x1 y1) (2, 1)), hCAdd (hCMul x0 y1) (hCMul x1 y0))

hQAdd, hQSub :: HQ -> HQ -> HQ
hQAdd (a, b) (c, d) = (hCAdd a c, hCAdd b d)
hQSub (a, b) (c, d) = (hCSub a c, hCSub b d)

hQScale :: HQ -> Integer -> HQ
hQScale ((a, b), (c, d)) s = ((hMul a s, hMul b s), (hMul c s, hMul d s))

hFold :: HQ -> HQ -> Integer -> HQ -> HQ
hFold fx fnx xinv alpha = hQAdd (hQAdd fx fnx) (hQMul alpha (hQScale (hQSub fx fnx) xinv))

toQ :: HQ -> QM31
toQ ((a, b), (c, d)) = ((w32 a, w32 b), (w32 c, w32 d))

-- Vectors ---------------------------------------------------------------------------

entries :: [Entry]
entries =
  [ kernel "stark-m31-mul" "M31 multiplication (Mersenne-31 field)" (\((a, b), c) -> Prog (witness ((w32 a, w32 b), w32 c) >>> (take m31Mul &&& ih >>> eq >>> verify)))
      ([ (((a, b), hMul a b), Accept) | (a, b) <- pairs ] ++ [ (((5, 7), 36), Reject) ])
  , kernel "stark-m31-inv" "M31 inversion by exponentiation (a^(p-2))" (\(a, c) -> Prog (witness (w32 a, w32 c) >>> (take m31Pow &&& ih >>> eq >>> verify)))
      ([ ((a, powMod a (p31 - 2)), Accept) | a <- [1, 2, 3, 123456789, p31 - 1] ] ++ [ ((2, 3), Reject) ])
  , kernel "stark-qm31-mul" "QM31 multiplication (degree-4 extension of M31)" (\((x, y), z) -> Prog (witness ((toQ x, toQ y), toQ z) >>> (take qm31Mul &&& ih >>> eq >>> verify)))
      ([ (((x, y), hQMul x y), Accept) | (x, y) <- qpairs ] ++ [ (((q1, q2), q1), Reject) ])
  , kernel "stark-fri-fold" "Circle FRI line fold of one evaluation pair" (\(((fx, fnx), (xi, al)), r) -> Prog (witness (((toQ fx, toQ fnx), (w32 xi, toQ al)), toQ r) >>> (take friFold &&& ih >>> eq >>> verify)))
      ([ ((((fx, fnx), (xi, al)), hFold fx fnx xi al), Accept) | (fx, fnx, xi, al) <- folds ] ++ [ ((((q1, q2), (5, q2)), q1), Reject) ])
  ]
 where
  pairs = [(0, 0), (1, p31 - 1), (p31 - 1, p31 - 1), (123456789, 987654321), (2 ^ (30 :: Int), 2)]
  q1 = ((1, 2), (3, 4))
  q2 = ((p31 - 1, 5), (77777, 2 ^ (30 :: Int)))
  qpairs = [(q1, q2), (q2, q2), (((0, 0), (0, 1)), ((0, 0), (0, 1)))]
  folds = [(q1, q2, 1234567, q2), (q2, q1, p31 - 3, q1)]
  powMod _ 0 = 1
  powMod b e | even e = let h = powMod b (e `div` 2) in h * h `mod` p31
             | otherwise = b * powMod b (e - 1) `mod` p31

kernel :: String -> String -> (w -> Prog) -> [(w, Expect)] -> Entry
kernel eid title prog vs = Entry
  { entryId = eid
  , entryTitle = title
  , entrySpec = "Circle STARK arithmetic over M31 = 2^31 - 1 (as in StarkWare's Stwo)"
  , entryCategory = Stark
  , entryVectorSource = Derived "expected values from a Haskell Integer reference"
  , entryAssumptions = ["inputs are canonical field elements; operands and the expected result are witness data"]
  , entryProgram = prog
  , entryVectors = [ Vector ("case " ++ show (i :: Int)) env w e | (i, (w, e)) <- zip [1 ..] vs ]
  }
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
