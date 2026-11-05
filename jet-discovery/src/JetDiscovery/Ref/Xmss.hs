-- | Independent ByteString/Integer reference for RFC 8391 XMSS-SHA2_10_256.
-- This is test tooling. Secret keys below are deterministic test-only data.
module JetDiscovery.Ref.Xmss
  ( Signature(..), publicSeed, publicRoot, signatureFor, verify, chain, digits
  , address, randomHash, fHash, hMsg, wotsLeaf
  ) where

import qualified Data.ByteString as BS
import Data.Bits (shiftR, (.&.), xor, testBit)
import Data.List (foldl')
import JetDiscovery.Tx (sha256,hashToBytes)
import qualified JetDiscovery.Ref.Bip340 as R

type B = BS.ByteString

data Signature = Signature { index :: Integer, randomness :: B, chains :: [B], auth :: [B] }
  deriving Show

hash :: B -> B
hash = hashToBytes . sha256

word32 :: Integer -> B
word32 = BS.drop 28 . R.bytesFromInt

-- RFC 8391 section 2.5. The type-specific four words follow 0,0,0,type.
address :: Integer -> Integer -> Integer -> Integer -> Integer -> B
address typ leaf height node km = BS.concat (map word32 [0,0,0,typ,leaf,height,node,km])

prf :: B -> B -> B
prf seed ad = hash (R.bytesFromInt 3 <> seed <> ad)

mask :: B -> B -> B
mask a b = BS.pack (BS.zipWith xor a b)

-- The address is passed in a form whose keyAndMask (last word) is overwritten.
withKm :: B -> Integer -> B
withKm ad km = BS.take 28 ad <> word32 km

fHash :: B -> B -> B -> B
fHash seed ad msg = hash (R.bytesFromInt 0 <> prf seed (withKm ad 0) <> mask msg (prf seed (withKm ad 1)))

randomHash :: B -> B -> B -> B -> B
randomHash seed ad left right = hash (R.bytesFromInt 1 <> prf seed (withKm ad 0) <>
                                     mask left (prf seed (withKm ad 1)) <>
                                     mask right (prf seed (withKm ad 2)))

hMsg :: B -> B -> Integer -> B -> B
hMsg r root idx msg = hash (R.bytesFromInt 2 <> r <> root <> R.bytesFromInt idx <> msg)

-- 64 big-endian nibbles followed by the three checksum nibbles.
digits :: B -> [Int]
digits digest = ns ++ [fromIntegral ((csum `shiftR` s) .&. 15) | s <- [8,4,0]]
 where
  ns = concat [[fromIntegral (b `shiftR` 4),fromIntegral (b .&. 15)] | b <- BS.unpack digest]
  csum = sum (map (15-) ns) :: Int

chain :: B -> Integer -> Int -> Int -> Int -> B -> B
chain seed idx chainIdx start count x = foldl' (\v step -> fHash seed (address 0 idx (toInteger chainIdx) (toInteger step) 0) v) x [start..start+count-1]

ltree :: B -> Integer -> [B] -> B
ltree seed idx = go 0
 where
  go _ [x] = x
  go h xs = go (h+1) (pairs 0 xs)
   where
    pairs _ [] = []
    pairs _ [x] = [x]
    pairs j (x:y:rest) = randomHash seed (address 1 idx h j 0) x y : pairs (j+1) rest

secret :: Int -> B
secret i = hash (R.bytesFromInt (0x83910000+toInteger i))

publicSeed :: B
publicSeed = hash (R.bytesFromInt 0x8391)

testIndex :: Integer
testIndex = 17

wotsLeaf :: B
wotsLeaf = ltree publicSeed testIndex [chain publicSeed testIndex i 0 15 (secret i) | i <- [0..66]]

authPath :: [B]
authPath = [hash (R.bytesFromInt (0xa0000+toInteger i)) | i <- [0..9]]

rootFrom :: B -> Integer -> B -> [B] -> B
rootFrom seed idx leaf siblings = foldl' level leaf (zip [0..] siblings)
 where
  level node (height,sibling) = let ad=address 2 0 (toInteger height) (idx `shiftR` (height+1)) 0 in
    if testBit idx height then randomHash seed ad sibling node else randomHash seed ad node sibling

publicRoot :: B
publicRoot = rootFrom publicSeed testIndex wotsLeaf authPath

signatureFor :: B -> Signature
signatureFor msg = Signature testIndex r sig authPath
 where
  r = hash (R.bytesFromInt 0x123456789)
  ds = digits (hMsg r publicRoot testIndex msg)
  sig = [chain publicSeed testIndex i 0 d (secret i) | (i,d) <- zip [0..] ds]

verify :: B -> Signature -> Bool
verify msg (Signature idx r sig path)
 | idx<0 || idx>=1024 || length sig/=67 || length path/=10 || BS.length r/=32 = False
 | any ((/=32).BS.length) (sig++path) = False
 | otherwise = rootFrom publicSeed idx leaf path == publicRoot
 where
  ds=digits (hMsg r publicRoot idx msg)
  leaf=ltree publicSeed idx [chain publicSeed idx i d (15-d) s | (i,(d,s))<-zip [0..] (zip ds sig)]
