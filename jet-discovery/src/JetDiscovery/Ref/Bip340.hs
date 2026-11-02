-- | A small, slow, self-contained BIP 340 reference implementation used to
-- create signatures for test vectors.  It follows the pseudocode in
-- vendor-specs/bips/bip-0340.mediawiki and is checked against
-- vendor-specs/bips/bip-0340_test-vectors.csv by the test suite.
--
-- This is test tooling, not consensus code.  It is not constant time.
module JetDiscovery.Ref.Bip340
  ( p, n, Pt, gPt, pointAdd, pointMul, liftX, xOnly, hasEvenY
  , pubkeyOf, sign, verify, intFromBytes, bytesFromInt
  , taggedHash
  , taprootTweak, embedData, nums
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.Bits (shiftL, shiftR, xor, testBit)

import JetDiscovery.Tx (sha256, hashToBytes)

p, n :: Integer
p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

type Pt = Maybe (Integer, Integer)

gPt :: Pt
gPt = Just ( 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
           , 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8 )

powMod :: Integer -> Integer -> Integer -> Integer
powMod _ 0 m = 1 `mod` m
powMod b e m | even e = let h = powMod b (e `div` 2) m in h * h `mod` m
             | otherwise = b * powMod b (e - 1) m `mod` m

inv :: Integer -> Integer -> Integer
inv a m = powMod a (m - 2) m

pointAdd :: Pt -> Pt -> Pt
pointAdd Nothing q = q
pointAdd q Nothing = q
pointAdd (Just (x1, y1)) (Just (x2, y2))
  | x1 == x2 && y1 /= y2 = Nothing
  | otherwise = Just (x3, (lam * (x1 - x3) - y1) `mod` p)
 where
  lam | x1 == x2 && y1 == y2 = 3 * x1 * x1 * inv (2 * y1) p `mod` p
      | otherwise = (y2 - y1) * inv (x2 - x1) p `mod` p
  x3 = (lam * lam - x1 - x2) `mod` p

pointMul :: Pt -> Integer -> Pt
pointMul pt k = go pt k Nothing
 where
  go _ 0 acc = acc
  go q e acc = go (pointAdd q q) (e `shiftR` 1) (if testBit e 0 then pointAdd acc q else acc)

hasEvenY :: (Integer, Integer) -> Bool
hasEvenY (_, y) = even y

liftX :: Integer -> Pt
liftX x | x >= p = Nothing
        | (y * y) `mod` p /= c = Nothing
        | otherwise = Just (x, if even y then y else p - y)
 where
  c = (x * x * x + 7) `mod` p
  y = powMod c ((p + 1) `div` 4) p

xOnly :: Pt -> Integer
xOnly (Just (x, _)) = x
xOnly Nothing = error "xOnly: point at infinity"

intFromBytes :: BS.ByteString -> Integer
intFromBytes = BS.foldl' (\a w -> a `shiftL` 8 + toInteger w) 0

bytesFromInt :: Integer -> BS.ByteString
bytesFromInt x = BS.pack [ fromIntegral (x `shiftR` (8 * i)) | i <- [31, 30 .. 0] ]

taggedHash :: String -> BS.ByteString -> BS.ByteString
taggedHash tag msg = hashToBytes (sha256 (t <> t <> msg))
 where t = hashToBytes (sha256 (BSC.pack tag))

-- | x-only public key of a secret key.
pubkeyOf :: Integer -> Integer
pubkeyOf d = xOnly (pointMul gPt d)

-- | BIP 340 signing with auxiliary randomness.  Messages may have any length.
sign :: Integer -> BS.ByteString -> BS.ByteString -> BS.ByteString
sign d0 msg aux
  | d0 < 1 || d0 >= n = error "sign: bad secret key"
  | k0 == 0 = error "sign: k = 0"
  | otherwise = bytesFromInt rx <> bytesFromInt s
 where
  Just pP = pointMul gPt d0
  d = if hasEvenY pP then d0 else n - d0
  t = d `xor` intFromBytes (taggedHash "BIP0340/aux" aux)
  k0 = intFromBytes (taggedHash "BIP0340/nonce" (bytesFromInt t <> bytesFromInt (fst pP) <> msg)) `mod` n
  Just rR = pointMul gPt k0
  k = if hasEvenY rR then k0 else n - k0
  rx = fst rR
  e = intFromBytes (taggedHash "BIP0340/challenge" (bytesFromInt rx <> bytesFromInt (fst pP) <> msg)) `mod` n
  s = (k + e * d) `mod` n

verify :: BS.ByteString -> BS.ByteString -> BS.ByteString -> Bool
verify pk msg sig
  | BS.length pk /= 32 || BS.length sig /= 64 = False
  | otherwise = case liftX (intFromBytes pk) of
      Nothing -> False
      pP -> r < p && s < n && case pointAdd (pointMul gPt s) (pointMul pP (n - e)) of
              Just rR -> hasEvenY rR && fst rR == r
              Nothing -> False
       where
        e = intFromBytes (taggedHash "BIP0340/challenge" (BS.take 32 sig <> pk <> msg)) `mod` n
 where
  r = intFromBytes (BS.take 32 sig)
  s = intFromBytes (BS.drop 32 sig)

-- | BIP 341 NUMS point x-coordinate.
nums :: Integer
nums = 0x50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0

-- | BIP 341 @taproot_tweak_pubkey@: x-only output key for internal key @pk@ and Merkle root @h@ (32 bytes).
taprootTweak :: Integer -> BS.ByteString -> Integer
taprootTweak pk h = xOnly (pointAdd (liftX pk) (pointMul gPt t))
 where t = intFromBytes (taggedHash "TapTweak" (bytesFromInt pk <> h)) `mod` n

-- | BIP 443 @tweak_embed_data@ (non-empty data): x-only key @lift_x(pk) + sha256(pk || data) G@.
embedData :: Integer -> BS.ByteString -> Integer
embedData pk dat = xOnly (pointAdd (liftX pk) (pointMul gPt t))
 where t = intFromBytes (hashToBytes (sha256 (bytesFromInt pk <> dat))) `mod` n
