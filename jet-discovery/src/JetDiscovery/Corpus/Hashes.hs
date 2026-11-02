{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}
-- | Hash functions other chains rely on, written with the existing word jets:
--
-- * BLAKE2s-256 and BLAKE2b-512 compression (RFC 7693).  BLAKE2b's
--   compression function F is Ethereum's EIP-152 precompile; BLAKE2s is the
--   core of BLAKE3 and of several STARK hash choices.
-- * Keccak-f[1600] and Keccak-256 (Ethereum's hash).
module JetDiscovery.Corpus.Hashes
  ( entries
  , debugBlake2s
  ) where

import Prelude hiding (drop, take, not, and, or, Word)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.Bits (testBit, shiftL, (.&.), complement)
import qualified Data.Bits as Bits
import qualified Data.List as L

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.Word as Word
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes (konst, w8)
import JetDiscovery.Tx
import JetDiscovery.Types

-- Paths into nested pairs (no 'comp' nodes) ------------------------------------

pick :: (Core term, TyC x, TyC c) => Bool -> term x c -> term (x, x) c
pick True = drop
pick False = take

at16 :: (Core term, TyC a) => Int -> term (Vector16 a) a
at16 i = pick (testBit i 3) (pick (testBit i 2) (pick (testBit i 1) (pick (testBit i 0) iden)))

at32 :: (Core term, TyC a) => Int -> term (Vector32 a) a
at32 i = pick (testBit i 4) (at16' i)
 where at16' j = pick (testBit j 3) (pick (testBit j 2) (pick (testBit j 1) (pick (testBit j 0) iden)))

mk16 :: (Core term, TyC i, TyC a) => [term i a] -> term i (Vector16 a)
mk16 ts = mk8 (L.take 8 ts) &&& mk8 (L.drop 8 ts)
 where
  mk8 xs = mk4 (L.take 4 xs) &&& mk4 (L.drop 4 xs)
  mk4 xs = mk2 (L.take 2 xs) &&& mk2 (L.drop 2 xs)
  mk2 [a, b] = a &&& b
  mk2 _ = error "mk16"

mk32 :: (Core term, TyC i, TyC a) => [term i a] -> term i (Vector32 a)
mk32 ts = mk16 (L.take 16 ts) &&& mk16 (L.drop 16 ts)

-- 4-tuples (a, (b, (c, d))): select component k of the tuple produced by t
sel4 :: (Core term, TyC i, TyC a) => Int -> term i (a, (a, (a, a))) -> term i a
sel4 0 t = t >>> oh
sel4 1 t = t >>> ioh
sel4 2 t = t >>> iioh
sel4 _ t = t >>> iiih

-- a path version (no comp): component k of an input 4-tuple, then continue with t
q4 :: (Core term, TyC a, TyC c) => Int -> term a c -> term (a, (a, (a, a))) c
q4 0 t = take t
q4 1 t = drop (take t)
q4 2 t = drop (drop (take t))
q4 _ t = drop (drop (drop t))

-- BLAKE2 ----------------------------------------------------------------------

data Blake w a = Blake { bWord :: Word a, bRounds :: Int, bRot :: (Integer, Integer, Integer, Integer), bIV :: [Integer], bBits :: Int }

blake2s :: Blake Word32 Word32
blake2s = Blake word32 10 (16, 12, 8, 7)
  [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19] 32

blake2b :: Blake Word64 Word64
blake2b = Blake word64 12 (32, 24, 16, 63)
  [ 0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1
  , 0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179 ] 64

-- | Message schedule, copied from RFC 7693 Appendix C (vendor-specs/rfc/rfc7693.txt).
sigma :: [[Int]]
sigma =
  [ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
  , [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3]
  , [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4]
  , [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8]
  , [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13]
  , [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9]
  , [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11]
  , [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10]
  , [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5]
  , [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0] ]

-- | BLAKE2 compression F(h, m, t, f=final) compared with the expected h'.
-- Witness: h (8 words), m (16 words), t (2 words), expected (8 words).
blake2Compress :: forall term a w. (Assert term, Witness term, TyC a) => Blake w a -> ([a], [a], (a, a), [a]) -> term () ()
blake2Compress b w = fst (blake2Parts b w)

-- | (the full check, the state after n rounds) -- the second is for debugging.
blake2Parts :: forall term a w. (Assert term, Witness term, TyC a) => Blake w a -> ([a], [a], (a, a), [a]) -> (term () (), Int -> term () (Vector16 a))
blake2Parts b (hw, mw, (t0, t1), expected) = (v0 >>> rounds >>> finalOk, \n -> v0 >>> foldr (\r k -> round_ r >>> k) iden [0 .. n - 1])
 where
  w = bWord b
  (r1, r2, r3, r4) = bRot b
  add' :: TyC i => term i (a, a) -> term i a
  add' t = t >>> Arith.add w >>> ih
  xor' :: TyC i => term i (a, a) -> term i a
  xor' t = t >>> Word.bitwise_xor w
  rotr :: Integer -> term a a
  rotr n = konst (w8 n) &&& iden >>> Word.right_rotate word8 w
  kw :: TyC i => Integer -> term i a
  kw n = konst (toWord w n)
  iv = bIV b
  allOnes = 2 ^ bBits b - 1
  v0 :: term () (Vector16 a)
  v0 = mk16 ([ witness x | x <- hw ] ++ map kw (L.take 4 iv)
             ++ [ xor' (kw (iv !! 4) &&& witness t0), xor' (kw (iv !! 5) &&& witness t1)
                , kw ((iv !! 6) `Bits.xor` allOnes), kw (iv !! 7) ])
  -- the G function on (a, (b, (c, d))) with message words x, y
  gq :: a -> a -> term (a, (a, (a, a))) (a, (a, (a, a)))
  gq x y = stepA (witness x) >>> stepD r1 >>> stepC >>> stepB r2 >>> stepA (witness y) >>> stepD r3 >>> stepC >>> stepB r4
   where
    stepA m = add' (add' (oh &&& ioh) &&& m) &&& ih
    stepD r = oh &&& (ioh &&& (iioh &&& (xor' (iiih &&& oh) >>> rotr r)))
    stepC = oh &&& (ioh &&& (add' (iioh &&& iiih) &&& iiih))
    stepB r = oh &&& ((xor' (ioh &&& iioh) >>> rotr r) &&& iih)
  -- one half round: four independent G calls on the given lanes, then reassemble
  half :: [[Int]] -> [(a, a)] -> term (Vector16 a) (Vector16 a)
  half lanes ms = gs >>> mk16 [ placeOf l | l <- [0 .. 15] ]
   where
    gOf ([a', b', c', d'], (x, y)) = (at16 a' &&& (at16 b' &&& (at16 c' &&& at16 d'))) >>> gq x y
    gOf _ = error "blake2: lanes"
    [g0, g1, g2, g3] = map gOf (zip lanes ms)
    gs = g0 &&& (g1 &&& (g2 &&& g3))
    placeOf l = case [ (j, k) | (j, ls) <- zip [0 ..] lanes, (k, l') <- zip [0 ..] ls, l' == l ] of
      [(j, k)] -> q4 j (q4 k iden)
      _ -> error "blake2: lane"
  round_ r = half [[0,4,8,12],[1,5,9,13],[2,6,10,14],[3,7,11,15]] [ (mw !! (s !! (2 * i)), mw !! (s !! (2 * i + 1))) | i <- [0 .. 3] ]
         >>> half [[0,5,10,15],[1,6,11,12],[2,7,8,13],[3,4,9,14]] [ (mw !! (s !! (2 * i)), mw !! (s !! (2 * i + 1))) | i <- [4 .. 7] ]
   where s = sigma !! (r `mod` 10)
  rounds = foldr (\r k -> round_ r >>> k) iden [0 .. bRounds b - 1]
  -- h'[i] = h[i] ^ v[i] ^ v[i+8] must equal the expected word
  finalOk = foldr1 (\x y -> (x &&& y) >>> unit)
              [ ((xor' (xor' (witness (hw !! i) &&& at16 i) &&& at16 (i + 8))) &&& witness (expected !! i)) >>> eq >>> verify | i <- [0 .. 7] ]

-- Keccak ------------------------------------------------------------------------

keccakRC :: [Integer]
keccakRC =
  [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B, 0x0000000080000001
  , 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A
  , 0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080
  , 0x000000000000800A, 0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]

-- rotation offsets r[x][y], lane index x + 5y
keccakRot :: Int -> Int -> Int
keccakRot x y = [[0,36,3,41,18],[1,44,10,45,2],[62,6,43,15,61],[28,55,25,21,56],[27,20,39,8,14]] !! x !! y

-- | Keccak-f[1600] on 25 lanes stored in a Vector32 Word64 (lanes 25..31 are zero).
keccakF :: forall term. Assert term => term (Vector32 Word64) (Vector32 Word64)
keccakF = foldr (\r k -> keccakRound r >>> k) iden [0 .. 23]
 where
  xor' :: TyC i => term i (Word64, Word64) -> term i Word64
  xor' t = t >>> Word.bitwise_xor word64
  rotl :: Int -> term Word64 Word64
  rotl 0 = iden
  rotl n = konst (w8 (toInteger n)) &&& iden >>> Word.left_rotate word8 word64
  zero :: TyC i => term i Word64
  zero = konst (toWord64 0)
  pad7 :: TyC i => [term i Word64]
  pad7 = replicate 7 zero
  -- theta
  colParity x = foldr1 (\a b -> xor' (a &&& b)) [ at32 (x + 5 * y) | y <- [0 .. 4] ]
  cs = colParity 0 &&& (colParity 1 &&& (colParity 2 &&& (colParity 3 &&& colParity 4)))
  c5 :: Int -> term (Word64, (Word64, (Word64, (Word64, Word64)))) Word64
  c5 0 = oh
  c5 1 = ioh
  c5 2 = iioh
  c5 3 = iiioh
  c5 _ = iiiih
  ds = d 0 &&& (d 1 &&& (d 2 &&& (d 3 &&& d 4)))
   where d x = xor' (c5 ((x + 4) `mod` 5) &&& (c5 ((x + 1) `mod` 5) >>> rotl 1))
  theta = iden &&& (cs >>> ds) >>> mk32 ([ xor' (take (at32 i) &&& drop (c5 (i `mod` 5))) | i <- [0 .. 24] ] ++ pad7)
  -- rho and pi: B[y + 5 ((2x + 3y) mod 5)] = rotl(A[x + 5y], r[x][y])
  rhoPi = mk32 ([ src j | j <- [0 .. 24] ] ++ pad7)
   where src j = head [ at32 (x + 5 * y) >>> rotl (keccakRot x y) | x <- [0 .. 4], y <- [0 .. 4], y + 5 * ((2 * x + 3 * y) `mod` 5) == j ]
  -- chi and iota
  chiIota r = mk32 ([ lane i | i <- [0 .. 24] ] ++ pad7)
   where
    lane i = let (y, x) = i `divMod` 5
                 b k = at32 (((x + k) `mod` 5) + 5 * y)
                 v = xor' (b 0 &&& ((b 1 >>> Word.complement word64) &&& b 2 >>> Word.bitwise_and word64))
             in if i == 0 then xor' (v &&& konst (toWord64 (keccakRC !! r))) else v
  keccakRound r = theta >>> rhoPi >>> chiIota r

-- extra selectors for 5-tuples
iiioh :: (Core term, TyC a, TyC b, TyC c, TyC d, TyC e) => term (a, (b, (c, (d, e)))) d
iiioh = drop (drop (drop (take iden)))
iiiih :: (Core term, TyC a, TyC b, TyC c, TyC d, TyC e) => term (a, (b, (c, (d, e)))) e
iiiih = drop (drop (drop (drop iden)))

-- | Keccak-256 of a message of at most 135 bytes (one block), compared with the expected digest.
keccak256 :: (Assert term, Witness term) => ([Word64], [Word64]) -> term () ()
keccak256 (block, expected) = state0 >>> keccakF >>> outOk
 where
  state0 = mk32 ([ witness l | l <- block ] ++ replicate (32 - length block) (konst (toWord64 0)))
  outOk = foldr1 (\x y -> (x &&& y) >>> unit) [ (at32 i &&& witness (expected !! i)) >>> eq >>> verify | i <- [0 .. 3] ]

-- Vectors -----------------------------------------------------------------------

leWords :: Int -> BS.ByteString -> [Integer]
leWords n bs = [ BS.foldr (\b a -> a * 256 + toInteger b) 0 (BS.take n (BS.drop (n * i) bs)) | i <- [0 .. BS.length bs `div` n - 1] ]

keccakBlock :: BS.ByteString -> [Word64]
keccakBlock msg = map toWord64 (leWords 8 padded)
 where
  rate = 136
  body = msg <> BS.pack [0x01] <> BS.replicate (rate - BS.length msg - 1) 0
  padded = BS.take (rate - 1) body <> BS.pack [BS.last body `Bits.xor` 0x80]

entries :: [Entry]
entries =
  [ blakeEntry "xchain-blake2s-compress" "BLAKE2s-256 compression of \"abc\"" blake2s 4
      "50 8C 5E 8C 32 7C 14 E2 E1 A7 2B A3 4E EB 45 2F 37 45 8B 20 9E D6 3A 29 4D 99 9B 4C 86 67 59 82" (0x01010020) toWord32
  , blakeEntry "xchain-blake2b-compress" "BLAKE2b-512 compression of \"abc\" (EIP-152 F)" blake2b 8
      ("BA 80 A5 3F 98 1C 4D 0D 6A 27 97 B6 9F 12 F6 E9 4C 21 2F 14 68 5A C4 B7 4B 12 BB 6F DB FF A2 D1 "
       ++ "7D 87 C5 39 2A AB 79 2D C2 52 D5 DE 45 33 CC 95 18 D3 8A A8 DB F1 92 5A B9 23 86 ED D4 00 99 23") (0x01010040) toWord64
  , Entry
    { entryId = "xchain-keccak256"
    , entryTitle = "Keccak-256 of a one-block message (Keccak-f[1600], 24 rounds)"
    , entrySpec = "Keccak-256 as used by Ethereum (Keccak team's original padding 0x01 ... 0x80)"
    , entryCategory = CrossChain
    , entryVectorSource = Derived "well-known Keccak-256 answers for \"\" and \"abc\" (as used throughout Ethereum tooling)"
    , entryAssumptions = ["message of at most 135 bytes (one 1088-bit block)", "message block and expected digest are witness operands"]
    , entryProgram = \w -> Prog (keccak256 w)
    , entryVectors =
        [ Vector "Keccak-256(\"\")" env (keccakBlock BS.empty, expect "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470") Accept
        , Vector "Keccak-256(\"abc\")" env (keccakBlock (BSC.pack "abc"), expect "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45") Accept
        , Vector "wrong digest" env (keccakBlock (BSC.pack "abd"), expect "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45") Reject
        ]
    }
  ]
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  expect h = map toWord64 (leWords 8 (unhex h))

blakeEntry :: TyC a => String -> String -> Blake w a -> Int -> String -> Integer -> (Integer -> a) -> Entry
blakeEntry eid title b n digestHex param toW = Entry
  { entryId = eid
  , entryTitle = title
  , entrySpec = "RFC 7693 (vendor-specs/rfc/rfc7693.txt)"
  , entryCategory = CrossChain
  , entryVectorSource = Upstream "vendor-specs/rfc/rfc7693.txt, Appendix A/B (\"abc\")"
  , entryAssumptions = ["one compression call with the final-block flag; h, m, t and the expected h' are witness operands"]
  , entryProgram = \w -> Prog (blake2Compress b w)
  , entryVectors =
      [ Vector "\"abc\"" env (h0, m, (toW 3, toW 0), expected) Accept
      , Vector "\"abc\" with a wrong byte counter" env (h0, m, (toW 4, toW 0), expected) Reject ]
  }
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  h0 = map toW (((head (bIV b)) `Bits.xor` param) : L.drop 1 (bIV b))
  m = map toW (leWords n (BSC.pack "abc" <> BS.replicate (16 * n - 3) 0))
  digest = unhex (filter (/= ' ') digestHex)
  expected = map toW (leWords n digest)

debugBlake2s :: (Assert term, Witness term) => Int -> term () (Vector16 Word32)
debugBlake2s n = snd (blake2Parts blake2s (h0, m, (toWord32 3, toWord32 0), replicate 8 (toWord32 0))) n
 where
  h0 = map toWord32 (((head (bIV blake2s)) `Bits.xor` 0x01010020) : L.drop 1 (bIV blake2s))
  m = map toWord32 (leWords 4 (BSC.pack "abc" <> BS.replicate 61 0))
