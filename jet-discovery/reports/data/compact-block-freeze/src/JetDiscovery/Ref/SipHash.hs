-- | Independent byte-oriented SipHash-2-4. Arithmetic uses Word64 wrapping.
module JetDiscovery.Ref.SipHash (sipHash24) where
import qualified Data.ByteString as B
import Data.Bits (xor,rotateL,shiftL)
import Data.Word (Word64)
import Data.List (foldl')

type State=(Word64,Word64,Word64,Word64)
roundS :: State -> State
roundS (a,b,c,d)=(a2,b2,rotateL c2 32,d2)
 where
  a1=rotateL (a+b) 32
  b1=rotateL b 13 `xor` (a+b)
  c1=c+d
  d1=rotateL d 16 `xor` c1
  a2=a1+d1
  d2=rotateL d1 21 `xor` a2
  c2=c1+b1
  b2=rotateL b1 17 `xor` c2
absorb :: State -> Word64 -> State
absorb (a,b,c,d) m=let (x,y,z,w)=roundS(roundS(a,b,c,d `xor` m)) in(x `xor` m,y,z,w)
little :: B.ByteString -> Word64
little=foldl' (\v (i,b)->v+(fromIntegral b `shiftL` (8*i))) 0 . zip [0..] . B.unpack
sipHash24 :: Word64 -> Word64 -> B.ByteString -> Word64
sipHash24 k0 k1 message=a `xor` b `xor` c `xor` d
 where
  initial=(k0 `xor` 0x736f6d6570736575,k1 `xor` 0x646f72616e646f6d,k0 `xor` 0x6c7967656e657261,k1 `xor` 0x7465646279746573)
  n=B.length message;complete=n-n `mod`8
  state=foldl' absorb initial [little(B.take 8(B.drop i message))|i<-[0,8..complete-1]]
  lastWord=little(B.drop complete message)+(fromIntegral(n `mod`256) `shiftL`56)
  (x,y,z,w)=absorb state lastWord
  (a,b,c,d)=iterate roundS (x,y,z `xor`255,w)!!4
