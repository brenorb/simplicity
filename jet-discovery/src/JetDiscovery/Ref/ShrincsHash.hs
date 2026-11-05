-- | Haskell byte/compression specification for the direct SHRINCS WOTS jet.
-- Uses the independent Data.Digest.Pure.SHA backend wrapped by Digest, not a
-- Simplicity evaluator. Every supplied midstate is supported, not just seeds.
module JetDiscovery.Ref.ShrincsHash
 ( chainSpec,seedStateSpec,encodePrefix,SeededCase,seededCases ) where
import qualified Data.ByteString as BS
import Data.Serialize (decode,encode)
import Data.Bits (shiftR)
import Simplicity.Digest

type SeededCase=(BS.ByteString,(Integer,Integer,Integer,Integer,Integer),Int,BS.ByteString)

be :: Int -> Integer -> BS.ByteString
be n x=BS.pack [fromIntegral (x `shiftR` (8*i))|i<-[n-1,n-2..0]]
asHash :: BS.ByteString -> Hash256
asHash x=case decode x of Right h->h;Left e->error e
compressBytes :: BS.ByteString -> BS.ByteString -> BS.ByteString
compressBytes state block=encode (ivHash (compress (freeStart (asHash state)) (asHash (BS.take 32 block),asHash (BS.drop 32 block))))

-- | Seed expansion compresses exactly one block, without finalization.
seedStateSpec :: BS.ByteString -> Maybe BS.ByteString
seedStateSpec seed
 | BS.length seed/=16=Nothing
 | otherwise=Just (encode (ivHash (compress noTagIv (asHash (seed<>BS.replicate 16 0),asHash (BS.replicate 32 0)))))

encodePrefix :: (Integer,Integer,Integer,Integer,Integer) -> Maybe BS.ByteString
encodePrefix (layer,tree,domain,keypair,chain)
 | and [x>=0 && x<2^(8*n)|(n,x)<-fields]=Just (BS.concat [be n x|(n,x)<-fields])
 | otherwise=Nothing
 where fields=[(1,layer),(8,tree),(1,domain),(4,keypair),(4,chain)]

chainSpec :: BS.ByteString -> BS.ByteString -> Int -> BS.ByteString -> Maybe BS.ByteString
chainSpec state prefix start node
 | BS.length state/=32 || BS.length prefix/=18 || start<0 || start>15 || BS.length node/=16=Nothing
 | otherwise=Just (foldl step node [start..14])
 where
  step value j=BS.take 16 (compressBytes state (prefix<>be 4 (toInteger j)<>value<>padding))
  padding=BS.singleton 128<>BS.replicate 17 0<>be 8 816

-- |18 seeded cases: bottom/top stateless addresses and an actual stateful
-- height/index/type16 address, first/last chain and starts0/7/15.
seededCases :: [SeededCase]
seededCases=[(BS.replicate 16 0x5e,(layer,tree,domain,keypair,chain),start,BS.replicate 16 0x37)
 |(layer,tree,domain,keypair)<-[(0,2^35+12345,0,511),(4,0,0,1),(251,5,16,0)],chain<-[0,34],start<-[0,7,15]]
