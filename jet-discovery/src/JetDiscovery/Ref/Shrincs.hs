-- | A Haskell transcription of the SHRINCS stateful path from
-- vendor-specs/shrincs/SHRINCS.md (draft at SHRINCS/shrincs-bip@4fe68e3):
-- tweakable hashes, WOTS+C, FXMSS verification, and @shrincs_verify@'s
-- stateful branch.  Each function mirrors the Python of the same name.
--
-- For test vectors we also need signatures.  FXMSS verification only depends
-- on the signing leaf and its authentication path, so 'signStateful' builds a
-- real WOTS+C leaf (secret chains from PRF, grinding as in
-- @wots_c_grind_to_constant_sum@) and an arbitrary authentication path, and
-- returns the matching public key.
module JetDiscovery.Ref.Shrincs
  ( fxmssHeight, chainCount, chainBits, constantSum
  , fT, hT, tSf, hGrind, hMsgSf, prf, prfMsgSf
  , base2b, mapDigest, grind
  , wotsChainIter, wotsPkFromSig
  , fxmssPkFromSig, verifyStateful
  , StatefulSig(..), signStateful, sigBytes
  ) where

import qualified Data.ByteString as BS
import Data.Bits (shiftL, shiftR, xor, (.&.), testBit)
import Data.Word (Word8, Word64)

import JetDiscovery.Tx (sha256, hashToBytes)

fxmssHeight, chainCount, chainBits, constantSum :: Int
fxmssHeight = 255
chainCount = 32
chainBits = 4
constantSum = 240

be :: Int -> Integer -> BS.ByteString
be n x = BS.pack [ fromIntegral (x `shiftR` (8 * i)) | i <- [n - 1, n - 2 .. 0] ]

zeros :: Int -> BS.ByteString
zeros n = BS.replicate n 0

sha :: BS.ByteString -> BS.ByteString
sha = hashToBytes . sha256

-- | Address.pack: height(1) || index(8) || type(1) || word1(4) || word2(4) || word3(4).
adrs :: Int -> Integer -> Int -> Integer -> Integer -> Integer -> BS.ByteString
adrs h idx ty w1 w2 w3 = be 1 (toInteger h) <> be 8 idx <> be 1 (toInteger ty) <> be 4 w1 <> be 4 w2 <> be 4 w3

sfWotsCHash, sfWotsCPk, sfFxmssTree, sfWotsCPrf, sfWotsCGrind :: Int
sfWotsCHash = 16
sfWotsCPk = 17
sfFxmssTree = 18
sfWotsCPrf = 21
sfWotsCGrind = 22

tweak :: BS.ByteString -> BS.ByteString -> BS.ByteString -> BS.ByteString
tweak pkSeed a m = BS.take 16 (sha (pkSeed <> zeros 48 <> a <> m))

-- | F with a WotsCHash address.
fT :: BS.ByteString -> Int -> Integer -> Integer -> Integer -> BS.ByteString -> BS.ByteString
fT pkSeed h idx chain j = tweak pkSeed (adrs h idx sfWotsCHash 0 chain j)

-- | H with an FxmssTree address.
hT :: BS.ByteString -> Int -> Integer -> BS.ByteString -> BS.ByteString
hT pkSeed h idx = tweak pkSeed (adrs h idx sfFxmssTree 0 0 0)

-- | T_sf with a WotsCPk address.
tSf :: BS.ByteString -> Int -> Integer -> BS.ByteString -> BS.ByteString
tSf pkSeed h idx = tweak pkSeed (adrs h idx sfWotsCPk 0 0 0)

-- | H_grind: only the leading 10 bytes of the WotsCGrind address are hashed.
hGrind :: BS.ByteString -> Int -> Integer -> BS.ByteString -> Int -> BS.ByteString
hGrind pkSeed h idx digest counter =
  BS.take 16 (sha (pkSeed <> zeros 48 <> BS.take 10 (adrs h idx sfWotsCGrind 0 0 0) <> digest <> zeros 4 <> be 2 (toInteger counter)))

hMsgSf :: BS.ByteString -> BS.ByteString -> BS.ByteString -> Int -> Integer -> BS.ByteString -> BS.ByteString
hMsgSf r pkSeed sfRoot h idx m = sha (r <> pkSeed <> sha (r <> pkSeed <> sfRoot <> leaf <> m) <> leaf)
 where leaf = be 1 (toInteger h) <> be 8 idx

-- | PRF with a WotsCPrf address.
prf :: BS.ByteString -> BS.ByteString -> Int -> Integer -> Bool -> Int -> Integer -> BS.ByteString
prf pkSeed skSeed h idx balanced depth chain =
  tweak pkSeed (adrs h idx sfWotsCPrf ((if balanced then 2 ^ (24 :: Int) else 0) + toInteger depth * 2 ^ (16 :: Int)) chain 0) skSeed

hmacSha256 :: BS.ByteString -> BS.ByteString -> BS.ByteString
hmacSha256 key msg = sha (BS.map (xor 0x5c) k <> sha (BS.map (xor 0x36) k <> msg))
 where k = key <> zeros (64 - BS.length key)

prfMsgSf :: BS.ByteString -> BS.ByteString -> Int -> Integer -> BS.ByteString -> BS.ByteString
prfMsgSf skPrf pkSeed h idx m = BS.take 16 (hmacSha256 (skPrf <> BS.replicate 48 0xff) (pkSeed <> be 1 (toInteger h) <> be 8 idx <> m))

base2b :: BS.ByteString -> Int -> Int -> [Int]
base2b x b outlen = go 0 0 0 outlen
 where
  go _ _ _ 0 = []
  go j acc bits k
    | bits < b = go (j + 1) (acc `shiftL` 8 + fromIntegral (BS.index x j)) (bits + 8) k
    | otherwise = let bits' = bits - b in (acc `shiftR` bits') : go j (acc .&. (2 ^ bits' - 1)) bits' (k - 1)

mapDigest :: BS.ByteString -> BS.ByteString -> Int -> Integer -> Int -> Maybe [Int]
mapDigest pkSeed digest h idx counter
  | sum is == constantSum = Just is
  | otherwise = Nothing
 where is = base2b (hGrind pkSeed h idx digest counter) chainBits chainCount

grind :: BS.ByteString -> BS.ByteString -> Int -> Integer -> Maybe (Int, [Int])
grind pkSeed digest h idx = case [ (c, is) | c <- [0 .. 2 ^ (16 :: Int) - 1], Just is <- [mapDigest pkSeed digest h idx c] ] of
  (r:_) -> Just r
  [] -> Nothing

wotsChainIter :: BS.ByteString -> Int -> Int -> BS.ByteString -> Int -> Integer -> Integer -> BS.ByteString
wotsChainIter node start stop pkSeed h idx chain = foldl (\n j -> fT pkSeed h idx chain (toInteger j) n) node [start .. stop - 1]

-- | wots_c_pubkey_from_sig: counter (2 bytes) || 32 chain values.
wotsPkFromSig :: BS.ByteString -> BS.ByteString -> BS.ByteString -> Int -> Integer -> Maybe BS.ByteString
wotsPkFromSig sig digest pkSeed h idx = do
  is <- mapDigest pkSeed digest h idx (fromInteger (intOf (BS.take 2 sig)))
  let tips = [ wotsChainIter (BS.take 16 (BS.drop (2 + 16 * i) sig)) d (2 ^ chainBits - 1) pkSeed h idx (toInteger i) | (i, d) <- zip [0 ..] is ]
  return (tSf pkSeed h idx (BS.concat tips))

intOf :: BS.ByteString -> Integer
intOf = BS.foldl' (\a w -> a `shiftL` 8 + toInteger w) 0

fxmssPkFromSig :: Integer -> Int -> BS.ByteString -> BS.ByteString -> BS.ByteString -> Maybe BS.ByteString
fxmssPkFromSig idx h sig digest pkSeed = do
  let depth = fxmssHeight - h
      auth = BS.drop (2 + 16 * chainCount) sig
  if BS.length auth /= depth * 16 || idx >= 2 ^ min 64 depth then Nothing else do
    leaf <- wotsPkFromSig (BS.take (2 + 16 * chainCount) sig) digest pkSeed h idx
    return $ foldl (\node k -> let sib = BS.take 16 (BS.drop (16 * k) auth)
                                   parentH = h + k + 1
                                   parentI = idx `shiftR` (k + 1)
                               in if testBit idx k then hT pkSeed parentH parentI (sib <> node)
                                                   else hT pkSeed parentH parentI (node <> sib))
                   leaf [0 .. depth - 1]

-- | The stateful branch of shrincs_verify with an empty context.
verifyStateful :: BS.ByteString -> BS.ByteString -> BS.ByteString -> Bool
verifyStateful msg sig pubkey
  | BS.length pubkey /= 48 || BS.null sig = False
  | indicator >= fxmssHeight = False
  | BS.length sig < 548 || BS.length sig > 4619 = False
  | idx >= 2 ^ min 64 depth = False
  | BS.length fx /= 2 + 16 * chainCount + depth * 16 = False
  | otherwise = fxmssPkFromSig idx indicator fx digest pkSeed == Just sfRoot
 where
  pkSeed = BS.take 16 pubkey
  slRoot = BS.take 16 (BS.drop 16 pubkey)
  sfRoot = BS.drop 32 pubkey
  indicator = fromIntegral (BS.head sig)
  r = BS.take 16 (BS.drop 1 sig)
  depth = fxmssHeight - indicator
  idxSize = (min depth 64 + 7) `div` 8
  idx = intOf (BS.take idxSize (BS.drop 17 sig))
  fx = BS.drop (17 + idxSize) sig
  bound = BS.pack [0, 0] <> slRoot <> msg
  digest = hMsgSf r pkSeed sfRoot indicator idx bound

data StatefulSig = StatefulSig
  { ssHeight :: Int, ssIndex :: Integer, ssR :: BS.ByteString, ssCounter :: Int
  , ssChains :: [BS.ByteString], ssAuth :: [BS.ByteString] }

-- | Serialize as shrincs_sign does: indicator || R || leaf_index || counter || chains || auth path.
sigBytes :: StatefulSig -> BS.ByteString
sigBytes s = BS.pack [fromIntegral (ssHeight s)] <> ssR s <> be idxSize (ssIndex s) <> be 2 (toInteger (ssCounter s)) <> BS.concat (ssChains s) <> BS.concat (ssAuth s)
 where idxSize = (min (fxmssHeight - ssHeight s) 64 + 7) `div` 8

-- | Sign @msg@ (empty context) with the WOTS+C leaf at depth @depth@ and index @idx@,
-- using the given seeds and authentication path siblings.  Returns (signature, 48-byte public key).
signStateful :: (BS.ByteString, BS.ByteString, BS.ByteString) -> BS.ByteString -> Int -> Integer -> [BS.ByteString] -> BS.ByteString
             -> (StatefulSig, BS.ByteString)
signStateful (skSeed, skPrf, pkSeed) slRoot depth idx auth msg = (s, pkSeed <> slRoot <> sfRoot)
 where
  h = fxmssHeight - depth
  sk i = prf pkSeed skSeed h idx False depth (toInteger i)
  leafPk = tSf pkSeed h idx (BS.concat [ wotsChainIter (sk i) 0 15 pkSeed h idx (toInteger i) | i <- [0 .. chainCount - 1] ])
  sfRoot = foldl (\node k -> let sib = auth !! k in
                    if testBit idx k then hT pkSeed (h + k + 1) (idx `shiftR` (k + 1)) (sib <> node)
                                     else hT pkSeed (h + k + 1) (idx `shiftR` (k + 1)) (node <> sib))
                 leafPk [0 .. depth - 1]
  bound = BS.pack [0, 0] <> slRoot <> msg
  r = prfMsgSf skPrf pkSeed h idx bound
  digest = hMsgSf r pkSeed sfRoot h idx bound
  Just (counter, is) = grind pkSeed digest h idx
  chains = [ wotsChainIter (sk i) 0 d pkSeed h idx (toInteger i) | (i, d) <- zip [0 ..] is ]
  s = StatefulSig h idx r counter chains (take depth auth)
