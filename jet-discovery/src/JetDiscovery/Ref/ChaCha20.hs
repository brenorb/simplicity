-- | Independent indexed-array RFC8439 reference using machine Word32 wrapping.
module JetDiscovery.Ref.ChaCha20 (block,encrypt) where
import qualified Data.ByteString as B
import Data.Array (Array,listArray,elems,(!),(//))
import Data.Bits(xor,rotateL,shiftL,shiftR)
import Data.Word(Word32)
import Data.List(foldl')

little :: B.ByteString -> Word32
little bytes=sum[fromIntegral x `shiftL`(8*i)|(i,x)<-zip[0..](B.unpack bytes)]
words32 :: B.ByteString -> [Word32]
words32 bytes=[little(B.take 4(B.drop i bytes))|i<-[0,4..B.length bytes-1]]
serialize :: [Word32] -> B.ByteString
serialize=B.pack.concatMap(\x->[fromIntegral(x `shiftR`(8*i))|i<-[0..3]])
qr :: Array Int Word32 -> [Int] -> Array Int Word32
qr s [a,b,c,d]=s//[(a,a2),(b,b2),(c,c2),(d,d2)]
 where
  a1=s!a+s!b;d1=rotateL(s!d `xor` a1)16
  c1=s!c+d1;b1=rotateL(s!b `xor` c1)12
  a2=a1+b1;d2=rotateL(d1 `xor` a2)8
  c2=c1+d2;b2=rotateL(b1 `xor` c2)7
qr _ _=error "ChaCha20 reference lane"
block :: B.ByteString -> Word32 -> B.ByteString -> B.ByteString
block key counter nonce
 | B.length key/=32 || B.length nonce/=12=error "ChaCha20 key/nonce width"
 | otherwise=serialize(zipWith(+)(elems initial)(elems final))
 where
  initial=listArray(0,15)([0x61707865,0x3320646e,0x79622d32,0x6b206574]++words32 key++[counter]++words32 nonce)
  lanes=[[0,4,8,12],[1,5,9,13],[2,6,10,14],[3,7,11,15],[0,5,10,15],[1,6,11,12],[2,7,8,13],[3,4,9,14]]
  final=iterate(\s->foldl' qr s lanes)initial!!10
encrypt :: B.ByteString -> Word32 -> B.ByteString -> B.ByteString -> B.ByteString
encrypt key counter nonce message
 | toInteger counter+toInteger((B.length message+63)`div`64)>2^(32::Int)=error "ChaCha20 counter exhaustion"
 | otherwise=B.pack(B.zipWith xor message stream)
 where stream=B.concat[block key(counter+fromIntegral i)nonce|i<-[0..(B.length message+63)`div`64-1]]
