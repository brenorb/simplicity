{-# LANGUAGE ScopedTypeVariables #-}
-- | The RIPEMD-160 compression function as a Simplicity expression (the
-- @ripemd160_compress@ candidate's specification).  Kept apart from the corpus
-- program so the candidate registry can import it.
module JetDiscovery.Lib.Ripemd160
  ( W5
  , ripemd160Compress
  , ripemdIV, ivT, toW5, mk16, pick
  , rL, rR, sL, sR, kL, kR
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.List as L

import Simplicity.Term.Core
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.Word as Word
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes

type W5 = (Word32, (Word32, (Word32, (Word32, Word32))))

rL, rR, sL, sR :: [Int]
rL = [0..15] ++ [7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8] ++ [3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12]
  ++ [1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2] ++ [4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13]
rR = [5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12] ++ [6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2] ++ [15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13]
  ++ [8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14] ++ [12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11]
sL = [11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8] ++ [7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12] ++ [11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5]
  ++ [11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12] ++ [9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6]
sR = [8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6] ++ [9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11] ++ [9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5]
  ++ [15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8] ++ [8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11]

kL, kR :: [Integer]
kL = [0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]
kR = [0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

ripemdIV :: [Integer]
ripemdIV = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]

pick :: (Core term, TyC x, TyC c) => Bool -> term x c -> term (x, x) c
pick True = drop
pick False = take

at16 :: (Core term, TyC a) => Int -> term (Vector16 a) a
at16 i = pick (odd (i `div` 8)) (pick (odd (i `div` 4)) (pick (odd (i `div` 2)) (pick (odd i) iden)))

-- | Component k of a 5-tuple, continuing with t (a path, no comp).
q5 :: (Core term, TyC a, TyC c) => Int -> term a c -> term (a, (a, (a, (a, a)))) c
q5 0 t = take t
q5 1 t = drop (take t)
q5 2 t = drop (drop (take t))
q5 3 t = drop (drop (drop (take t)))
q5 _ t = drop (drop (drop (drop t)))

-- | RIPEMD-160 compression: input (h, X) with X the 16 little-endian message words; output h'.
ripemd160Compress :: forall term. Assert term => term (W5, Vector16 Word32) W5
ripemd160Compress = (iden &&& (line rL sL kL id &&& line rR sR kR (\g -> 4 - g))) >>> final
 where
  add' :: TyC i => term i (Word32, Word32) -> term i Word32
  add' t = t >>> Arith.add word32 >>> ih
  xor', and', or' :: TyC i => term i (Word32, Word32) -> term i Word32
  xor' t = t >>> Word.bitwise_xor word32
  and' t = t >>> Word.bitwise_and word32
  or' t = t >>> Word.bitwise_or word32
  cpl :: TyC i => term i Word32 -> term i Word32
  cpl t = t >>> Word.complement word32
  rol :: Int -> term Word32 Word32
  rol n = konst (w8 (toInteger n)) &&& iden >>> Word.left_rotate word8 word32
  -- the five boolean functions on (x, (y, z))
  f :: Int -> term (Word32, (Word32, Word32)) Word32
  f 0 = xor' (xor' (oh &&& ioh) &&& iih)
  f 1 = or' (and' (oh &&& ioh) &&& and' (cpl oh &&& iih))
  f 2 = xor' (or' (oh &&& cpl ioh) &&& iih)
  f 3 = or' (and' (oh &&& iih) &&& and' (ioh &&& cpl iih))
  f _ = xor' (oh &&& or' (ioh &&& cpl iih))
  -- one step on (state, X): T = rol(a + f(b, c, d) + X[r] + K, s) + e; state := (e, T, b, rol(c, 10), d)
  step :: Int -> Int -> Integer -> Int -> term (W5, Vector16 Word32) W5
  step g r k s = take (q5 4 iden) &&& (t &&& (take (q5 1 iden) &&& ((take (q5 2 iden) >>> rol 10) &&& take (q5 3 iden))))
   where
    fv = (take (q5 1 iden) &&& (take (q5 2 iden) &&& take (q5 3 iden))) >>> f g
    s3 = add' (add' (add' (take (q5 0 iden) &&& fv) &&& drop (at16 r)) &&& konst (w32 k))
    t = add' ((s3 >>> rol s) &&& take (q5 4 iden))
  line :: [Int] -> [Int] -> [Integer] -> (Int -> Int) -> term (W5, Vector16 Word32) W5
  line rs ss ks fun = L.foldl' (\acc j -> (acc &&& ih) >>> step (fun (j `div` 16)) (rs !! j) (ks !! (j `div` 16)) (ss !! j)) oh [0 .. 79]
  -- input ((h, X), (left, right)):
  -- h0' = h1 + cL + dR, h1' = h2 + dL + eR, h2' = h3 + eL + aR, h3' = h4 + aL + bR, h4' = h0 + bL + cR
  hI k = take (take (q5 k iden))
  lI k = drop (take (q5 k iden))
  rI k = drop (drop (q5 k iden))
  sum3 a b c = add' (add' (a &&& b) &&& c)
  final = sum3 (hI 1) (lI 2) (rI 3) &&& (sum3 (hI 2) (lI 3) (rI 4) &&& (sum3 (hI 3) (lI 4) (rI 0) &&& (sum3 (hI 4) (lI 0) (rI 1) &&& sum3 (hI 0) (lI 1) (rI 2))))

mk16 :: (Core term, TyC i, TyC a) => [term i a] -> term i (Vector16 a)
mk16 ts = mk8 (L.take 8 ts) &&& mk8 (L.drop 8 ts)
 where
  mk8 xs = mk4 (L.take 4 xs) &&& mk4 (L.drop 4 xs)
  mk4 xs = mk2 (L.take 2 xs) &&& mk2 (L.drop 2 xs)
  mk2 [a, b] = a &&& b
  mk2 _ = error "mk16"

ivT :: (Core term, TyC i) => term i W5
ivT = konst (toW5 ripemdIV)

toW5 :: [Integer] -> W5
toW5 [a, b, c, d, e] = (w32 a, (w32 b, (w32 c, (w32 d, w32 e))))
toW5 _ = error "toW5"
