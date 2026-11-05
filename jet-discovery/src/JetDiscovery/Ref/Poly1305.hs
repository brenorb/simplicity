-- | Independent arbitrary-precision RFC8439 Poly1305 reference.
module JetDiscovery.Ref.Poly1305 (poly1305) where
import qualified Data.ByteString as B
import Data.Bits ((.&.),shiftL,shiftR)
import Data.List(foldl')
little bytes=sum[toInteger x `shiftL`(8*i)|(i,x)<-zip[0..](B.unpack bytes)]
poly1305 :: B.ByteString -> B.ByteString -> B.ByteString
poly1305 key message
 | B.length key/=32=error "Poly1305 key width"
 | otherwise=B.pack[fromIntegral(tag `shiftR`(8*i))|i<-[0..15]]
 where
  r=little(B.take 16 key).&.0x0ffffffc0ffffffc0ffffffc0fffffff
  s=little(B.drop 16 key)
  prime=2^(130::Int)-5
  chunks=[B.take 16(B.drop i message)|i<-[0,16..B.length message-1]]
  step acc chunk=((acc+little chunk+2^(8*B.length chunk))*r)`mod`prime
  tag=(foldl' step 0 chunks+s)`mod`2^(128::Int)
