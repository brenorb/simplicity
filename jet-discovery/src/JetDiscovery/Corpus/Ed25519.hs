{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
-- | SHA-512 and Ed25519 verification (RFC 8032), with the existing 64-bit word
-- jets only: a pure SHA-512 compression kernel; arithmetic mod 2^255 - 19;
-- extended twisted-Edwards coordinates with complete formulas
-- (dbl-2008-hwcd, add-2008-hwcd-3 with an affine point); and the joint
-- check [S]B - [k]A = R over 253 bits.  The x-coordinates of A and R are
-- witness hints checked against the curve equation and the sign bit.
module JetDiscovery.Corpus.Ed25519
  ( entries
  , sha512Compress
  , mulmod
  ) where

import Prelude hiding (drop, take, not, and, or, subtract)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.Bits (testBit, shiftL, shiftR, (.&.))
import qualified Data.List as L

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.Word as Word
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types

sha512K, sha512IV :: [Integer]
sha512K = [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc, 0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118, 0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2, 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694, 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0xfc19dc68b8cd5b5, 0x240ca1cc77ac9c65, 0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5, 0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4, 0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x6ca6351e003826f, 0x142929670a0e6e70, 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df, 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b, 0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30, 0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8, 0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8, 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3, 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec, 0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b, 0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178, 0x6f067aa72176fba, 0xa637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b, 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c, 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]
sha512IV = [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

pick :: (Core term, TyC x, TyC c) => Bool -> term x c -> term (x, x) c
pick True = drop
pick False = take

at8 :: (Core term, TyC a) => Int -> term (Vector8 a) a
at8 i = pick (testBit i 2) (pick (testBit i 1) (pick (testBit i 0) iden))

at16 :: (Core term, TyC a) => Int -> term (Vector16 a) a
at16 i = pick (testBit i 3) (at8' i) where at8' j = pick (testBit j 2) (pick (testBit j 1) (pick (testBit j 0) iden))

mk8 :: (Core term, TyC s, TyC a) => [term s a] -> term s (Vector8 a)
mk8 [a, b, c, d, e, f, g, h] = ((a &&& b) &&& (c &&& d)) &&& ((e &&& f) &&& (g &&& h))
mk8 _ = error "mk8"

mk16 :: (Core term, TyC s, TyC a) => [term s a] -> term s (Vector16 a)
mk16 xs = mk8 (L.take 8 xs) &&& mk8 (L.drop 8 xs)

-- SHA-512 ------------------------------------------------------------------------------

-- | SHA-512 compression: input (H, M) with H the 8-word state and M the 16-word block (big endian words).
sha512Compress :: forall term. Assert term => term (Vector8 Word64, Vector16 Word64) (Vector8 Word64)
sha512Compress = iden &&& (rounds >>> oh) >>> mk8 [ add' (take (take (at8 i)) &&& drop (at8 i)) | i <- [0 .. 7] ]
 where
  add' :: TyC i => term i (Word64, Word64) -> term i Word64
  add' t = t >>> Arith.add word64 >>> ih
  rotr :: Integer -> term Word64 Word64
  rotr n = konst (w8 n) &&& iden >>> Word.right_rotate word8 word64
  shr :: Integer -> term Word64 Word64
  shr n = konst (w8 n) &&& iden >>> Word.right_shift word8 word64
  xor3 a b c = (a &&& (b &&& c)) >>> Word.bitwise_xor_xor word64
  bSigma0 = xor3 (rotr 28) (rotr 34) (rotr 39)
  bSigma1 = xor3 (rotr 14) (rotr 18) (rotr 41)
  sSigma0 = xor3 (rotr 1) (rotr 8) (shr 7)
  sSigma1 = xor3 (rotr 19) (rotr 61) (shr 6)
  -- state (work, window); for t < 16 the window is the block and W_t = window[t];
  -- for t >= 16 the window holds W_{t-16} .. W_{t-1}
  rounds = (take iden &&& drop iden) >>> L.foldl' (\acc t -> acc >>> roundT t) iden [0 .. 79]
  roundT :: Int -> term (Vector8 Word64, Vector16 Word64) (Vector8 Word64, Vector16 Word64)
  roundT t | t < 16 = (iden &&& drop (at16 t)) >>> (compressStep t &&& take ih)
           | otherwise = (oh &&& (drop newW &&& drop iden >>> slide)) >>> (iden &&& drop (at16 15)) >>> (compressStep t &&& take ih)
  newW = add' (add' (add' ((at16 14 >>> sSigma1) &&& at16 9) &&& (at16 1 >>> sSigma0)) &&& at16 0)
  -- (new word, window) -> window shifted by one with the new word last
  slide = mk16 ([ drop (at16 i) | i <- [1 .. 15] ] ++ [oh])
  -- input ((work, window), W_t) -> work'
  compressStep :: Int -> term ((Vector8 Word64, Vector16 Word64), Word64) (Vector8 Word64)
  compressStep t = (iden &&& t1) >>> (iden &&& t2) >>> out
   where
    v i = take (take (at8 i))
    w = ih
    t1 = add' (add' (add' (add' (v 7 &&& (v 4 >>> bSigma1)) &&& ((v 4 &&& (v 5 &&& v 6)) >>> Word.bitwise_ch word64)) &&& konst (w64 (sha512K !! t))) &&& w)
    t2 = add' ((take (v 0) >>> bSigma0) &&& ((take (v 0) &&& (take (v 1) &&& take (v 2))) >>> Word.bitwise_maj word64))
    -- input ((base, T1), T2)
    vv i = take (take (v i))
    out = mk8 [ add' (take ih &&& ih), vv 0, vv 1, vv 2, add' (vv 3 &&& take ih), vv 4, vv 5, vv 6 ]

sha512IVT :: (Core term, TyC s) => term s (Vector8 Word64)
sha512IVT = mk8 [ konst (w64 h) | h <- sha512IV ]

-- Field mod 2^255 - 19 -----------------------------------------------------------------

p25519, d25519, l25519, bx25519, by25519 :: Integer
p25519 = 2 ^ (255 :: Int) - 19
d25519 = 37095705934669439343138083508754565189542113879843219016388785533085940283555
l25519 = 2 ^ (252 :: Int) + 27742317777372353535851937790883648493
bx25519 = 15112221349535400772501151409588531511454012693041857206046113283949847762202
by25519 = 46316835694926478169428394003475163141307993866256225615783033603165251855960

kw :: (Core term, TyC s) => Integer -> term s Word256
kw = konst . toWord256

canon :: Assert term => term Word256 Word256
canon = (iden &&& (iden &&& kw p25519 >>> Arith.subtract word256)) >>> (ioh &&& (oh &&& iih)) >>> cond oh ih

-- | (a + b) mod p for a, b < p (the sum fits in 256 bits).
addmod :: Assert term => term (Word256, Word256) Word256
addmod = Arith.add word256 >>> ih >>> canon

submod :: Assert term => term (Word256, Word256) Word256
submod = Arith.subtract word256 >>> cond (iden &&& kw p25519 >>> Arith.add word256 >>> ih) iden

-- | (a * b) mod p, folding the high half with 2^256 = 38 (mod p).
mulmod :: Assert term => term (Word256, Word256) Word256
mulmod = Arith.multiply word256 >>> fold1 >>> fold2 >>> canon >>> canon
 where
  -- (hi, lo) -> (k, s) with value = k 2^256 + s, k < 2^7
  fold1 = (take ((iden &&& kw 38) >>> Arith.multiply word256) &&& ih) >>> ((take oh) &&& ((take ih &&& ih) >>> Arith.add word256))
          >>> (oh &&& ih) >>> (((ioh &&& oh) >>> cond ((iden &&& kw 1) >>> Arith.add word256 >>> ih) iden) &&& iih)
  -- (k, s) -> s + 38 k (+ 38 on carry)
  fold2 = ((take ((iden &&& kw 38) >>> Arith.multiply word256 >>> ih)) &&& ih) >>> (ih &&& oh >>> Arith.add word256)
          >>> cond ((iden &&& kw 38) >>> Arith.add word256 >>> ih) iden

add2, sub2, mul2 :: (Assert term, TyC s) => term s Word256 -> term s Word256 -> term s Word256
add2 a b = (a &&& b) >>> addmod
sub2 a b = (a &&& b) >>> submod
mul2 a b = (a &&& b) >>> mulmod

-- Edwards points (a = -1) ------------------------------------------------------------------

-- | Extended coordinates ((X, Y), (Z, T)).
type Ext = ((Word256, Word256), (Word256, Word256))
-- | Precomputed affine point (y - x, (y + x, 2 d x y)).
type Pre = (Word256, (Word256, Word256))

-- | dbl-2008-hwcd for a = -1: A = X^2, B = Y^2, C = 2 Z^2, E = (X + Y)^2 - A - B, G = B - A, F = G - C, H = -A - B.
dblE :: forall term. Assert term => term Ext Ext
dblE = st >>> out
 where
  sqr t = t >>> (iden &&& iden >>> mulmod)
  -- st: (point, ((A, B), C))
  st = iden &&& (((ooh >>> sqr iden) &&& (oih >>> sqr iden)) &&& (ioh >>> sqr iden >>> (iden &&& iden >>> addmod)))
  a = drop ooh
  b = drop oih
  c = drop ih
  e = sub2 (sub2 (add2 (take ooh) (take oih) >>> sqr iden) a) b
  g = sub2 b a
  f = sub2 g c
  h = sub2 (sub2 (kw 0) a) b
  out = (mul2 e f &&& mul2 g h) &&& (mul2 f g &&& mul2 e h)

-- | add-2008-hwcd-3 with an affine precomputed point.
maddE :: forall term. Assert term => term (Ext, Pre) Ext
maddE = st >>> out
 where
  x1 = take ooh
  y1 = take oih
  z1 = take ioh
  t1 = take iih
  -- st: (input, ((A, B), (C, D)))
  st = iden &&& ((mul2 (sub2 y1 x1) (drop oh) &&& mul2 (add2 y1 x1) (drop ioh)) &&& (mul2 t1 (drop iih) &&& add2 z1 z1))
  a = drop ooh
  b = drop oih
  c = drop ioh
  d = drop iih
  e = sub2 b a
  f = sub2 d c
  g = add2 d c
  h = add2 b a
  out = (mul2 e f &&& mul2 g h) &&& (mul2 f g &&& mul2 e h)

-- | Reverse the 32 bytes of a 256-bit word, and the 64 of a 512-bit word.
rev256 :: Core term => term Word256 Word256
rev256 = drop r128 &&& take r128
 where
  r128 = drop r64 &&& take r64
  r64 = drop bswap32 &&& take bswap32

rev512 :: Core term => term Word512 Word512
rev512 = drop rev256 &&& take rev256

-- | Little-endian point encoding (from big-endian packed bytes) -> (y, sign bit).
decodeY :: Assert term => term Word256 (Word256, Bit)
decodeY = rev256 >>> (((iden &&& kw (2 ^ (255 :: Int) - 1)) >>> Word.bitwise_and word256) &&& (oh >>> oh >>> oh >>> oh >>> oh >>> oh >>> oh >>> oh))

-- | The hint x is a valid decompression of (y, sign): x, y < p, -x^2 + y^2 = 1 + d x^2 y^2, x mod 2 = sign.
onCurve :: Assert term => term (Word256, (Word256, Bit)) ()
onCurve = (((lt oh &&& lt ioh) &&& curve) &&& parity) >>> unit
 where
  lt t = (t &&& kw p25519 >>> Arith.subtract word256) >>> oh >>> verify
  x2 = mul2 oh oh
  y2 = mul2 ioh ioh
  curve = (sub2 y2 x2 &&& add2 (kw 1) (mul2 (kw d25519) (mul2 x2 y2))) >>> eq >>> verify
  parity = (oh >>> drop (drop (drop (drop (drop (drop (drop (drop iden)))))))) &&& iih >>> eq >>> verify

bit256 :: Core term => Int -> term Word256 Bit
bit256 i = pick (testBit q 7) (pick (testBit q 6) (pick (testBit q 5) (pick (testBit q 4) (pick (testBit q 3) (pick (testBit q 2) (pick (testBit q 1) (pick (testBit q 0) iden)))))))
 where q = 255 - i

-- | Ed25519 verification.  Witness: (block, (xR, (xA, S))): the single SHA-512 block holding
-- R || A || M (|M| <= 15) and its padding, the decompression hints, and S.
ed25519Verify :: forall term. (Assert term, Witness term) => (Vector16 Word64, (Word256, (Word256, Word256))) -> term () ()
ed25519Verify (blkv, (xrv, (xav, sv))) = checks &&& (scalars >>> loop >>> final) >>> unit
 where
  blk :: forall a. TyC a => term a (Vector16 Word64)
  blk = witness blkv
  xR, xA, s :: forall a. TyC a => term a Word256
  xR = witness xrv
  xA = witness xav
  s = witness sv
  rEnc, aEnc :: forall a. TyC a => term a Word256
  rEnc = blk >>> take oh    -- the first four 64-bit words (32 bytes)
  aEnc = blk >>> take ih
  yR, yA :: forall a. TyC a => term a (Word256, Bit)
  yR = rEnc >>> decodeY
  yA = aEnc >>> decodeY
  checks = (((xR &&& yR) >>> onCurve) &&& ((xA &&& yA) >>> onCurve)) &&& ((s &&& kw l25519 >>> Arith.subtract word256) >>> oh >>> verify) >>> unit
  -- k = SHA-512(R || A || M) as a little-endian integer, mod L
  hashLE = (sha512IVT &&& blk) >>> sha512Compress >>> rev512
  k = (hashLE &&& (kw 0 &&& kw l25519)) >>> Arith.div_mod word512 >>> ih >>> ih
  -- -A precomputed: (y + x, (y - x, -2 d x y))
  aNeg = (yA >>> oh) &&& xA >>> (add2 oh ih &&& (sub2 oh ih &&& sub2 (kw 0) (mul2 (kw (2 * d25519 `mod` p25519)) (mul2 ih oh))))
  bPre :: forall a. TyC a => term a Pre
  bPre = kw ((by25519 - bx25519) `mod` p25519) &&& (kw ((by25519 + bx25519) `mod` p25519) &&& kw (2 * d25519 * bx25519 * by25519 `mod` p25519))
  -- state ((S, k), (-A precomputed, acc)); acc starts at the identity (0, 1, 1, 0)
  scalars = (s &&& k) &&& (aNeg &&& ((kw 0 &&& kw 1) &&& (kw 1 &&& kw 0)))
  -- step: acc := 2 acc; + (-A) if bit i of k; + B if bit i of S.  On X = (state, doubled acc).
  step i = oh &&& (drop oh &&& ((iden &&& (drop ih >>> dblE)) >>> acc3))
   where
    bitS = take (take (take (bit256 i)))
    bitK = take (take (drop (bit256 i)))
    acc2 = (bitK &&& (ih &&& take (drop oh))) >>> cond maddE oh
    acc3 = (bitS &&& (acc2 &&& bPre)) >>> cond maddE oh
  loop = L.foldl' (\acc i -> acc >>> step i) iden [252, 251 .. 0] >>> drop ih
  -- the result equals R: X = xR Z and Y = yR Z
  final = (((ooh &&& mul2 xR ioh) >>> eq >>> verify) &&& ((oih &&& mul2 (yR >>> oh) ioh) >>> eq >>> verify)) >>> unit

-- Vectors -------------------------------------------------------------------------------

powP :: Integer -> Integer -> Integer
powP _ 0 = 1
powP b e | even e = let h = powP b (e `div` 2) in h * h `mod` p25519
         | otherwise = b * powP b (e - 1) `mod` p25519

-- | Decompress the x coordinate of an encoded point (RFC 8032 5.1.3).
decompressX :: BS.ByteString -> Integer
decompressX enc = if (x1 `mod` 2 == 1) /= sign then (p25519 - x1) `mod` p25519 else x1
 where
  yv = leInt enc .&. (2 ^ (255 :: Int) - 1)
  sign = testBit (leInt enc) 255
  u = (yv * yv - 1) `mod` p25519
  v = (d25519 * yv * yv + 1) `mod` p25519
  x2 = u * powP v (p25519 - 2) `mod` p25519
  x0 = powP x2 ((p25519 + 3) `div` 8)
  x1 = if (x0 * x0 - x2) `mod` p25519 == 0 then x0 else x0 * powP 2 ((p25519 - 1) `div` 4) `mod` p25519

leInt :: BS.ByteString -> Integer
leInt = BS.foldr (\b a -> a * 256 + toInteger b) 0

beWords :: BS.ByteString -> [Integer]
beWords bs = [ BS.foldl' (\a b -> a * 256 + toInteger b) 0 (BS.take 8 (BS.drop (8 * i) bs)) | i <- [0 .. BS.length bs `div` 8 - 1] ]

v16 :: [Integer] -> Vector16 Word64
v16 ws = let v8 [a, b, c, d, e, f, g, h] = (((w64 a, w64 b), (w64 c, w64 d)), ((w64 e, w64 f), (w64 g, w64 h)))
             v8 _ = error "v8"
         in (v8 (L.take 8 ws), v8 (L.drop 8 ws))

-- | One SHA-512 block holding the message (at most 111 bytes) and its padding.
sha512Block :: BS.ByteString -> Vector16 Word64
sha512Block m = v16 (beWords (m <> BS.pack [0x80] <> BS.replicate (111 - BS.length m) 0 <> BS.pack [ fromIntegral ((8 * BS.length m) `shiftR` (8 * i)) | i <- [15, 14 .. 0] ]))

entries :: [Entry]
entries =
  [ Entry
    { entryId = "xchain-sha512"
    , entryTitle = "SHA-512 compression of a one-block message"
    , entrySpec = "FIPS 180-4 SHA-512 (used by Ed25519)"
    , entryCategory = CrossChain
    , entryVectorSource = Derived "the published SHA-512 digest of \"abc\""
    , entryAssumptions = ["message of at most 111 bytes; block and expected digest are witness operands"]
    , entryProgram = \(m, d) -> Prog (witness (sha512Block m, v8w (beWords d)) >>> (((sha512IVT &&& oh) >>> sha512Compress) &&& ih) >>> eq >>> verify)
    , entryVectors =
        [ Vector "SHA-512(\"abc\")" env (BSC.pack "abc", abcDigest) Accept
        , Vector "wrong digest" env (BSC.pack "abd", abcDigest) Reject ]
    }
  , Entry
    { entryId = "xchain-ed25519"
    , entryTitle = "Ed25519 signature verification (RFC 8032) with word jets only"
    , entrySpec = "RFC 8032 Ed25519 (vendor-specs/rfc/rfc8032.txt), cofactorless check [S]B = R + [k]A"
    , entryCategory = CrossChain
    , entryVectorSource = Upstream "vendor-specs/rfc/rfc8032.txt section 7.1 TEST 1-3, plus 3 negative vectors"
    , entryAssumptions = [ "messages of at most 15 bytes (R || A || M in one SHA-512 block)"
                         , "the x coordinates of R and A are witness hints checked against the curve and the sign bit; key, message and signature are witness operands" ]
    , entryProgram = \w -> Prog (ed25519Verify w)
    , entryVectors =
        [ Vector "RFC 8032 TEST 1 (empty message)" env (vec t1pk t1sig BS.empty) Accept
        , Vector "RFC 8032 TEST 2 (1 byte)" env (vec t2pk t2sig (unhex "72")) Accept
        , Vector "RFC 8032 TEST 3 (2 bytes)" env (vec t3pk t3sig (unhex "af82")) Accept
        , Vector "TEST 2 signature on another message" env (vec t2pk t2sig (unhex "73")) Reject
        , Vector "TEST 3 with S + 1" env (let (b, (xr, (xa, sS))) = vec t3pk t3sig (unhex "af82") in (b, (xr, (xa, toWord256 (fromWord256 sS + 1))))) Reject
        , Vector "wrong decompression hint" env (let (b, (_, rest)) = vec t1pk t1sig BS.empty in (b, (toWord256 1, rest))) Reject ]
    }
  ]
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  abcDigest = unhex "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
  v8w [a, b, c, d, e, f, g, h] = (((w64 a, w64 b), (w64 c, w64 d)), ((w64 e, w64 f), (w64 g, w64 h)))
  v8w _ = error "v8w"
  t1pk = unhex "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
  t1sig = unhex "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
  t2pk = unhex "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c"
  t2sig = unhex "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00"
  t3pk = unhex "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025"
  t3sig = unhex "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a"
  vec pk sig m = let r = BS.take 32 sig in
    (sha512Block (r <> pk <> m), (toWord256 (decompressX r), (toWord256 (decompressX pk), toWord256 (leInt (BS.drop 32 sig)))))
