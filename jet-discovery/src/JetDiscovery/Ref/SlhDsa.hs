-- | A Haskell transcription of SHRINCS's stateless path (SLH-DSA with SHRINCS
-- parameters: n = 16, w = 16, d = 5, h' = 9, k = 10, a = 13), from
-- vendor-specs/shrincs/SHRINCS.md: FORS, WOTS-TW, XMSS, the hypertree and
-- @slh_dsa_verify@.
--
-- 'signStateless' builds a signature that verifies: the top XMSS tree is
-- computed in full (512 WOTS-TW keys) so that @sl_root@ is a real root; lower
-- layers and FORS use real one-time keys at the selected leaves with arbitrary
-- authentication-path siblings (verification only follows the path).
module JetDiscovery.Ref.SlhDsa
  ( layers, xmssHeight, forsCount, forsHeight, chainCount
  , StatelessSig(..), signStateless, verifyStateless
  , digestMessage, wotsIndexes
  ) where

import qualified Data.ByteString as BS
import Data.Bits (shiftL, shiftR, testBit, (.&.))

import JetDiscovery.Ref.Shrincs (adrs, be, tweak, sha, zeros, base2b)

layers, xmssHeight, forsCount, forsHeight, chainCount, chainBits :: Int
layers = 5
xmssHeight = 9
forsCount = 10
forsHeight = 13
chainCount = 35
chainBits = 4

slWotsHash, slWotsPk, slXmssTree, slForsTree, slForsRoots, slWotsPrf, slForsPrf :: Int
slWotsHash = 0
slWotsPk = 1
slXmssTree = 2
slForsTree = 3
slForsRoots = 4
slWotsPrf = 5
slForsPrf = 6

f :: BS.ByteString -> Int -> Integer -> Integer -> Integer -> Integer -> BS.ByteString -> BS.ByteString
f pk layer tree kp chain j = tweak pk (adrs layer tree slWotsHash kp chain j)

chainIter :: BS.ByteString -> Int -> Integer -> Integer -> Integer -> BS.ByteString -> Int -> Int -> BS.ByteString
chainIter pk layer tree kp chain node start stop = foldl (\n j -> f pk layer tree kp chain (toInteger j) n) node [start .. stop - 1]

wotsIndexes :: BS.ByteString -> [Int]
wotsIndexes msg = is ++ [ (cs `shiftR` (4 * i)) .&. 15 | i <- [2, 1, 0] ]
 where
  is = base2b msg chainBits 32
  cs = 480 - sum is

wotsSk :: BS.ByteString -> BS.ByteString -> Int -> Integer -> Integer -> Integer -> BS.ByteString
wotsSk pk sk layer tree kp chain = tweak pk (adrs layer tree slWotsPrf kp chain 0) sk

wotsPkGen :: BS.ByteString -> BS.ByteString -> Int -> Integer -> Integer -> BS.ByteString
wotsPkGen pk sk layer tree kp = tweak pk (adrs layer tree slWotsPk kp 0 0)
  (BS.concat [ chainIter pk layer tree kp (toInteger i) (wotsSk pk sk layer tree kp (toInteger i)) 0 15 | i <- [0 .. chainCount - 1] ])

wotsSign :: BS.ByteString -> BS.ByteString -> Int -> Integer -> Integer -> BS.ByteString -> [BS.ByteString]
wotsSign pk sk layer tree kp msg = [ chainIter pk layer tree kp (toInteger i) (wotsSk pk sk layer tree kp (toInteger i)) 0 d | (i, d) <- zip [0 ..] (wotsIndexes msg) ]

wotsPkFromSig :: BS.ByteString -> Int -> Integer -> Integer -> [BS.ByteString] -> BS.ByteString -> BS.ByteString
wotsPkFromSig pk layer tree kp sig msg = tweak pk (adrs layer tree slWotsPk kp 0 0)
  (BS.concat [ chainIter pk layer tree kp (toInteger i) s d 15 | (i, (s, d)) <- zip [0 ..] (zip sig (wotsIndexes msg)) ])

hNode :: BS.ByteString -> Int -> Integer -> Int -> Integer -> BS.ByteString -> BS.ByteString
hNode pk layer tree height idx = tweak pk (adrs layer tree slXmssTree 0 (toInteger height) idx)

xmssRoot :: BS.ByteString -> Int -> Integer -> Integer -> BS.ByteString -> [BS.ByteString] -> BS.ByteString
xmssRoot pk layer tree kp leaf auth = foldl (\node k ->
    let sib = auth !! k
        parent = kp `shiftR` (k + 1)
    in if testBit kp k then hNode pk layer tree (k + 1) parent (sib <> node) else hNode pk layer tree (k + 1) parent (node <> sib))
  leaf [0 .. xmssHeight - 1]

forsNode :: BS.ByteString -> Integer -> Integer -> Int -> Integer -> BS.ByteString -> BS.ByteString
forsNode pk tree kp height idx = tweak pk (adrs 0 tree slForsTree kp (toInteger height) idx)

forsRootFromSig :: BS.ByteString -> Integer -> Integer -> [(BS.ByteString, [BS.ByteString])] -> BS.ByteString -> BS.ByteString
forsRootFromSig pk tree kp sig digest = tweak pk (adrs 0 tree slForsRoots kp 0 0) (BS.concat roots)
 where
  is = base2b digest forsHeight forsCount
  roots = [ let ti = toInteger i * 2 ^ forsHeight + toInteger ix
                leaf = forsNode pk tree kp 0 ti pre
            in foldl (\node j -> let sib = auth !! j
                                     parent = ti `shiftR` (j + 1)
                                 in if testBit ti j then forsNode pk tree kp (j + 1) parent (sib <> node) else forsNode pk tree kp (j + 1) parent (node <> sib))
                     leaf [0 .. forsHeight - 1]
          | (i, (ix, (pre, auth))) <- zip [0 :: Int ..] (zip is sig) ]

-- | H_msg_sl then the split into (FORS digest, tree index, leaf index).
digestMessage :: BS.ByteString -> BS.ByteString -> BS.ByteString -> BS.ByteString -> (BS.ByteString, Integer, Integer)
digestMessage r pk slRoot m = (BS.take 17 d, intOf (BS.take 5 (BS.drop 17 d)) `mod` 2 ^ (36 :: Int), intOf (BS.take 2 (BS.drop 22 d)) `mod` 2 ^ xmssHeight)
 where d = sha (r <> pk <> sha (r <> pk <> slRoot <> m) <> zeros 4)

intOf :: BS.ByteString -> Integer
intOf = BS.foldl' (\a w -> a `shiftL` 8 + toInteger w) 0

data StatelessSig = StatelessSig
  { slR :: BS.ByteString
  , slFors :: [(BS.ByteString, [BS.ByteString])]          -- ^ 10 x (secret preimage, 13 auth nodes)
  , slLayers :: [([BS.ByteString], [BS.ByteString])]        -- ^ 5 x (35 chain values, 9 auth nodes)
  }

-- | Verify per slh_dsa_verify with an empty context; @m@ is the bound message (sf_root || M for SHRINCS).
verifyStateless :: BS.ByteString -> BS.ByteString -> BS.ByteString -> StatelessSig -> Bool
verifyStateless pk slRoot m (StatelessSig r fors lys) = go 0 tree0 leaf0 forsPk lys == slRoot
 where
  ctxMsg = BS.pack [0, 0] <> m
  (fd, tree0, leaf0) = digestMessage r pk slRoot ctxMsg
  forsPk = forsRootFromSig pk tree0 leaf0 fors fd
  go _ _ _ msg [] = msg
  go j tree leaf msg ((chains, auth):rest) =
    let root = xmssRoot pk j tree leaf (wotsPkFromSig pk j tree leaf chains msg) auth
    in go (j + 1) (tree `shiftR` xmssHeight) (tree .&. (2 ^ xmssHeight - 1)) root rest

-- | Sign the bound message @m@ (empty context).  Returns (sl_root, signature).
signStateless :: BS.ByteString -> BS.ByteString -> BS.ByteString -> (BS.ByteString, StatelessSig)
signStateless sk pk m = (slRoot, StatelessSig r fors lys)
 where
  topLayer = layers - 1
  -- the full top tree (tree address 0: 36 bits of tree index never reach the top layer)
  topLeaves = [ wotsPkGen pk sk topLayer 0 kp | kp <- [0 .. 2 ^ xmssHeight - 1] ]
  levels = takeWhile (not . null) (iterate up topLeaves) where
    up xs = [ hNode pk topLayer 0 h (toInteger i) (a <> b) | (i, (a, b)) <- zip [0 :: Int ..] (pairs xs), let h = height xs ]
    height xs = xmssHeight + 1 - lg (length xs)
    lg n = length (takeWhile (> 1) (iterate (`div` 2) n))
    pairs (a:b:rest) = (a, b) : pairs rest
    pairs _ = []
  slRoot = head (last levels)
  topAuth kp = [ (levels !! k) !! fromInteger ((kp `shiftR` k) `xorOne` 1) | k <- [0 .. xmssHeight - 1] ]
  xorOne x _ = if testBit x 0 then x - 1 else x + 1
  r = BS.take 16 (sha (BS.pack [7] <> sk <> m))
  ctxMsg = BS.pack [0, 0] <> m
  (fd, tree0, leaf0) = digestMessage r pk slRoot ctxMsg
  forsIdx = base2b fd forsHeight forsCount
  forsSk i ix = tweak pk (adrs 0 tree0 slForsPrf leaf0 0 (toInteger i * 2 ^ forsHeight + toInteger ix)) sk
  fors = [ (forsSk i ix, [ BS.replicate 16 (fromIntegral (i * 16 + j)) | j <- [0 .. forsHeight - 1] ]) | (i, ix) <- zip [0 :: Int ..] forsIdx ]
  forsPk = forsRootFromSig pk tree0 leaf0 fors fd
  lys = build 0 tree0 leaf0 forsPk
  build j tree leaf msg
    | j == topLayer = [(wotsSign pk sk j tree leaf msg, topAuth leaf)]
    | otherwise =
        let chains = wotsSign pk sk j tree leaf msg
            auth = [ BS.replicate 16 (fromIntegral (0x80 + j * 16 + k)) | k <- [0 .. xmssHeight - 1] ]
            root = xmssRoot pk j tree leaf (wotsPkFromSig pk j tree leaf chains msg) auth
        in (chains, auth) : build (j + 1) (tree `shiftR` xmssHeight) (tree .&. (2 ^ xmssHeight - 1)) root
