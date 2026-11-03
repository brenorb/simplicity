{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
-- | ECDSA verification over NIST P-256 (secp256r1), as Ethereum's
-- P256VERIFY precompile (RIP-7212) and WebAuthn/passkeys use, written with the
-- existing 64-bit word jets only:
--
-- * field multiplication: 256x256 multiply, then NIST's Solinas reduction;
-- * Jacobian doubling (dbl-2001-b, a = -3) and mixed addition (madd-2007-bl);
-- * joint double-scalar multiplication u1 G + u2 Q over 256 bits;
-- * s^-1 mod n is a witness hint checked with one multiplication mod n, and
--   x(R) = r is checked projectively (X = r Z^2), so no inversion runs.
module JetDiscovery.Corpus.P256
  ( entries
  , pP256, nP256, mulmod, addmod, submod, dblJ, maddJ, mulmodN
  ) where

import Prelude hiding (drop, take, not, and, or, subtract)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.Bits (testBit)
import qualified Data.List as L

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types

pP256, nP256, bP256, gxP256, gyP256 :: Integer
pP256 = 2 ^ (256 :: Int) - 2 ^ (224 :: Int) + 2 ^ (192 :: Int) + 2 ^ (96 :: Int) - 1
nP256 = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
bP256 = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
gxP256 = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
gyP256 = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5

kw :: (Core term, TyC s) => Integer -> term s Word256
kw = konst . toWord256

pick :: (Core term, TyC x, TyC c) => Bool -> term x c -> term (x, x) c
pick True = drop
pick False = take

-- | 32-bit word t (0 = most significant) of a 512-bit value.
wordAt512 :: Core term => Int -> term Word512 Word32
wordAt512 t = pick (testBit t 3) (pick (testBit t 2) (pick (testBit t 1) (pick (testBit t 0) iden)))

-- | Bit i (0 = least significant) of a 256-bit value.
bit256 :: Core term => Int -> term Word256 Bit
bit256 i = pick (testBit p 7) (pick (testBit p 6) (pick (testBit p 5) (pick (testBit p 4) (pick (testBit p 3) (pick (testBit p 2) (pick (testBit p 1) (pick (testBit p 0) iden)))))))
 where p = 255 - i

mk8 :: (Core term, TyC s) => [term s Word32] -> term s Word256
mk8 [a, b, c, d, e, f, g, h] = ((a &&& b) &&& (c &&& d)) &&& ((e &&& f) &&& (g &&& h))
mk8 _ = error "mk8"

-- | x - p if x >= p, else x (for x < 2p).
canon :: Assert term => term Word256 Word256
canon = (iden &&& (iden &&& kw pP256 >>> Arith.subtract word256)) >>> (ioh &&& (oh &&& iih)) >>> cond oh ih

-- | (a + b) mod p for a, b < p.
addmod :: Assert term => term (Word256, Word256) Word256
addmod = Arith.add word256 >>> (oh &&& (ih &&& (ih &&& kw pP256 >>> Arith.subtract word256))) >>> cond iih ((ioh &&& (oh &&& iih)) >>> cond oh ih)

-- | (a - b) mod p for a, b < p.
submod :: Assert term => term (Word256, Word256) Word256
submod = Arith.subtract word256 >>> cond (iden &&& kw pP256 >>> Arith.add word256 >>> ih) iden

-- | (a * b) mod p: Solinas reduction of the 512-bit product.
mulmod :: Assert term => term (Word256, Word256) Word256
mulmod = Arith.multiply word256 >>> reduce
 where
  c i = wordAt512 (15 - i)
  z = konst (w32 0)
  s1 = mk8 [c 7, c 6, c 5, c 4, c 3, c 2, c 1, c 0]
  s2 = mk8 [c 15, c 14, c 13, c 12, c 11, z, z, z]
  s3 = mk8 [z, c 15, c 14, c 13, c 12, z, z, z]
  s4 = mk8 [c 15, c 14, z, z, z, c 10, c 9, c 8]
  s5 = mk8 [c 8, c 13, c 15, c 14, c 13, c 11, c 10, c 9]
  s6 = mk8 [c 10, c 8, z, z, z, c 13, c 12, c 11]
  s7 = mk8 [c 11, c 9, z, z, c 15, c 14, c 13, c 12]
  s8 = mk8 [c 12, z, c 10, c 9, c 8, c 15, c 14, c 13]
  s9 = mk8 [c 13, z, c 11, c 10, c 9, z, c 15, c 14]
  -- accumulate with the product carried alongside: state (product, acc)
  start = iden &&& (s1 >>> canon)
  plus s = oh &&& ((ih &&& (oh >>> s >>> canon)) >>> addmod)
  minus s = oh &&& ((ih &&& (oh >>> s >>> canon)) >>> submod)
  reduce = start >>> plus s2 >>> plus s2 >>> plus s3 >>> plus s3 >>> plus s4 >>> plus s5 >>> minus s6 >>> minus s7 >>> minus s8 >>> minus s9 >>> ih

sq :: Assert term => term Word256 Word256
sq = iden &&& iden >>> mulmod

-- | a * b mod n (any 256-bit operands), with the generic 512-bit division.
mulmodN :: Assert term => term (Word256, Word256) Word256
mulmodN = (Arith.multiply word256 &&& (kw 0 &&& kw nP256)) >>> Arith.div_mod word512 >>> ih >>> ih

type J = ((Word256, Word256), Word256)
type Aff = (Word256, Word256)

-- binary helpers on any input
add2, sub2, mul2 :: (Assert term, TyC s) => term s Word256 -> term s Word256 -> term s Word256
add2 a b = (a &&& b) >>> addmod
sub2 a b = (a &&& b) >>> submod
mul2 a b = (a &&& b) >>> mulmod

dbl2, x3', x4, x8 :: Assert term => term Word256 Word256
dbl2 = iden &&& iden >>> addmod
x3' = (dbl2 &&& iden) >>> addmod
x4 = dbl2 >>> dbl2
x8 = x4 >>> dbl2

-- | Jacobian doubling for a = -3 (EFD dbl-2001-b).
dblJ :: forall term. Assert term => term J J
dblJ = st1 >>> st2 >>> st3 >>> out
 where
  -- st1: (J, (delta, gamma))
  st1 = iden &&& ((ih >>> sq) &&& (oih >>> sq))
  -- st2: ((J, (delta, gamma)), (beta, alpha))
  st2 = iden &&& (mul2 (take ooh) (drop ih) &&& (mul2 (sub2 (take ooh) (drop oh)) (add2 (take ooh) (drop oh)) >>> x3'))
  -- st3: (st2, X3); X3 = alpha^2 - 8 beta
  st3 = iden &&& sub2 (drop ih >>> sq) (drop oh >>> x8)
  alpha = take (drop ih)
  beta = take (drop oh)
  gamma = take (take (drop ih))
  delta = take (take (drop oh))
  yJ = take (take (take oih))
  zJ = take (take (take ih))
  y3 = sub2 (mul2 alpha (sub2 (beta >>> x4) ih)) (gamma >>> sq >>> x8)
  z3 = sub2 (sub2 (add2 yJ zJ >>> sq) gamma) delta
  out = (ih &&& y3) &&& z3

-- | Jacobian + affine addition (EFD madd-2007-bl); the points must differ and not be negatives.
-- Each stage pushes one value: S_k = (S_{k-1}, v_k), base B = (J, Aff).
maddJ :: forall term. Assert term => term (J, Aff) J
maddJ = s1 >>> s2 >>> s3 >>> s4 >>> s5 >>> s6 >>> s7 >>> s8 >>> s9 >>> s10 >>> out
 where
  t1 x = take x
  t2 x = take (take x)
  t3 x = take (take (take x))
  t4 x = take (t3 x)
  t5 x = take (t4 x)
  t6 x = take (t5 x)
  t8 x = take (take (t6 x))
  t9 x = take (t8 x)
  t10 x = take (t9 x)
  -- on B: X1 = take ooh, Y1 = take oih, Z1 = take ih, X2 = drop oh, Y2 = drop ih
  s1 = iden &&& (take ih >>> sq)                                                -- Z1Z1
  s2 = iden &&& mul2 (t1 (drop oh)) ih                                          -- U2 = X2 Z1Z1
  s3 = iden &&& mul2 (mul2 (t2 (drop ih)) (t2 (take ih))) (t1 ih)               -- S2 = Y2 Z1 Z1Z1
  s4 = iden &&& sub2 (t1 ih) (t3 (take ooh))                                    -- H = U2 - X1
  s5 = iden &&& (sub2 (t1 ih) (t4 (take oih)) >>> dbl2)                         -- r = 2 (S2 - Y1)
  s6 = iden &&& (t1 ih >>> sq)                                                  -- HH = H^2
  s7 = iden &&& (ih >>> x4)                                                     -- I = 4 HH
  s8 = iden &&& mul2 (t3 ih) ih                                                 -- J' = H I
  s9 = iden &&& mul2 (t8 (take ooh)) (t1 ih)                                    -- V = X1 I
  s10 = iden &&& sub2 (sub2 (t4 ih >>> sq) (t1 ih)) (ih >>> dbl2)               -- X3 = r^2 - J' - 2 V
  y3 = sub2 (mul2 (t5 ih) (sub2 (t1 ih) ih)) (mul2 (t10 (take oih)) (t2 ih) >>> dbl2)   -- r (V - X3) - 2 Y1 J'
  z3 = sub2 (sub2 (add2 (t10 (take ih)) (t6 ih) >>> sq) (t9 ih)) (t4 ih)        -- (Z1 + H)^2 - Z1Z1 - HH
  out = (ih &&& y3) &&& z3

curveOk :: Assert term => term Aff ()
curveOk = (lhs &&& rhs) >>> eq >>> verify
 where
  lhs = ih >>> sq
  rhs = add2 (sub2 (mul2 (oh >>> sq) oh) (oh >>> x3')) (kw bP256)

-- | ECDSA-P256 verification of hash z.  Witness: (Q, (z, ((r, s), w))) with w = s^-1 mod n.
ecdsaP256 :: forall term. (Assert term, Witness term) => (Aff, (Word256, ((Word256, Word256), Word256))) -> term () ()
ecdsaP256 (qv, (zv, ((rv, sv), wv))) = checks &&& (scalars >>> loop >>> final) >>> unit
 where
  qT :: forall a. TyC a => term a Aff
  qT = witness qv
  r, s, w :: forall a. TyC a => term a Word256
  r = witness rv
  s = witness sv
  w = witness wv
  inRange x = ((x &&& kw 0 >>> eq >>> not iden >>> verify) &&& ((x &&& kw nP256 >>> Arith.subtract word256) >>> oh >>> verify)) >>> unit
  checks = (((qT >>> curveOk) &&& inRange r) &&& (inRange s &&& ((((s &&& w) >>> mulmodN) &&& kw 1) >>> eq >>> verify))) >>> unit
  scalars = (((witness zv &&& w) >>> mulmodN) &&& ((r &&& w) >>> mulmodN)) &&& (true &&& ((kw 0 &&& kw 0) &&& kw 0))
  gT :: forall a. TyC a => term a Aff
  gT = kw gxP256 &&& kw gyP256
  addPt :: (forall a. TyC a => term a Aff) -> term (Bit, J) (Bit, J)
  addPt pt = cond (false &&& (pt &&& kw 1)) (false &&& ((iden &&& pt) >>> maddJ))
  step i = oh &&& (((take (take (bit256 i))) &&& (((take (drop (bit256 i))) &&& (drop (oh &&& drop dblJ))) >>> cond (addPt qT) iden)) >>> cond (addPt gT) iden)
  loop = L.foldl' (\acc i -> acc >>> step i) iden [255, 254 .. 0] >>> ih
  -- R is not infinity, and X = r Z^2 or (r + n < p and X = (r + n) Z^2)
  final = ((oh >>> not iden >>> verify) &&& (ih >>> xOk)) >>> unit
  xOk = (iden &&& (ih >>> sq)) >>> ((take (take oh) &&& (r &&& ih >>> mulmod) >>> eq) &&& (rnOk)) >>> or oh ih >>> verify
  rnOk = ((r &&& kw nP256 >>> Arith.add word256) &&& iden) >>> ((take ih &&& kw pP256 >>> Arith.subtract word256 >>> oh) &&& ((drop (take (take oh)) &&& (take ih &&& drop ih >>> mulmod)) >>> eq)) >>> and oh ih

-- Haskell reference ---------------------------------------------------------------

powModN :: Integer -> Integer -> Integer -> Integer
powModN _ 0 m = 1 `mod` m
powModN b e m | even e = let h = powModN b (e `div` 2) m in h * h `mod` m
              | otherwise = b * powModN b (e - 1) m `mod` m

entries :: [Entry]
entries =
  [ Entry
    { entryId = "xchain-p256-ecdsa"
    , entryTitle = "ECDSA verification over NIST P-256 (RIP-7212 P256VERIFY / WebAuthn) with word jets only"
    , entrySpec = "FIPS 186-5 ECDSA over P-256; vectors from RFC 6979 A.2.5 (vendor-specs/rfc/rfc6979.txt)"
    , entryCategory = CrossChain
    , entryVectorSource = Upstream "vendor-specs/rfc/rfc6979.txt A.2.5: SHA-256 signatures of \"sample\" and \"test\", plus 3 negative vectors"
    , entryAssumptions = [ "the message hash z, public key Q, signature (r, s) and the hint w = s^-1 mod n are witness operands"
                         , "Jacobian formulas assume no exceptional additions (probability negligible for honest inputs)" ]
    , entryProgram = \(q, (zz, (rs, wh))) -> Prog (ecdsaP256 (pt q, (toWord256 zz, ((toWord256 (fst rs), toWord256 (snd rs)), toWord256 wh))))
    , entryVectors =
        [ Vector "RFC 6979 P-256, SHA-256, \"sample\"" env (vec "sample" sampleRS) Accept
        , Vector "RFC 6979 P-256, SHA-256, \"test\"" env (vec "test" testRS) Accept
        , Vector "signature of \"sample\" on \"test\"" env (let (q, (_, rest)) = vec "sample" sampleRS in (q, (hashOf "test", rest))) Reject
        , Vector "s changed" env (let (q, (zz, ((r', s'), _))) = vec "sample" sampleRS in (q, (zz, ((r', s' + 1), inv (s' + 1))))) Reject
        , Vector "public key not on the curve" env (let (_, rest) = vec "sample" sampleRS in ((ux, uy + 1), rest)) Reject ]
    }
  ]
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  ux = 0x60FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB6
  uy = 0x7903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299
  sampleRS = (0xEFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716, 0xF7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8)
  testRS = (0xF1ABB023518351CD71D881567B1EA663ED3EFCF6C5132B354F28D3B0B7D38367, 0x019F4113742A2B14BD25926B49C649155F267E60D3814B4C0CC84250E46F0083)
  hashOf m = BS.foldl' (\a b -> a * 256 + toInteger b) 0 (hashToBytes (sha256 (BSC.pack m)))
  inv x = powModN x (nP256 - 2) nP256
  vec m (r', s') = ((ux, uy), (hashOf m, ((r', s'), inv s')))
  pt (x, y) = (toWord256 x, toWord256 y)
