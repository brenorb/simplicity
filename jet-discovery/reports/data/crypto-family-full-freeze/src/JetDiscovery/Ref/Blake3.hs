-- | Independent byte/Word32 implementation of the bounded unkeyed BLAKE3
-- hash. Complete chunk chaining and binary parent root, not one compression.
module JetDiscovery.Ref.Blake3(hash256,compress,iv,patternInput) where
import qualified Data.ByteString as BS
import Data.Bits
import Data.Word
import qualified Data.List as L
iv :: [Word32]
iv=[0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19]
replace i x a=take i a++[x]++drop(i+1)a
-- Equations follow the BLAKE3 specification; all arithmetic wraps at32bits.
mix a b c d x y s=
 let a1=s!!a+s!!b+x;d1=rotateR(s!!d`xor`a1)16;c1=s!!c+d1;b1=rotateR(s!!b`xor`c1)12
     a2=a1+b1+y;d2=rotateR(d1`xor`a2)8;c2=c1+d2;b2=rotateR(b1`xor`c2)7
 in replace d d2(replace c c2(replace b b2(replace a a2 s)))
compress :: [Word32] -> [Word32] -> Word64 -> Word32 -> Word32 -> [Word32]
compress cv message counter blockLen flags
 | length cv/=8 || length message/=16=error "BLAKE3 compression dimensions"
 | otherwise=[v!!i`xor`v!!(i+8)|i<-[0..7]]++[v!!(i+8)`xor`cv!!i|i<-[0..7]]
 where
  initial=cv++take 4 iv++[fromIntegral counter,fromIntegral(counter`shiftR`32),blockLen,flags]
  permutation=[2,6,3,10,7,0,4,13,1,11,12,5,9,14,15,8]
  roundOne(s,m)=
   let s1=L.foldl'(\a(i,(b,c,d,e))->mix b c d e(m!!(2*i))(m!!(2*i+1))a)s
           (zip[0..][(0,4,8,12),(1,5,9,13),(2,6,10,14),(3,7,11,15),(0,5,10,15),(1,6,11,12),(2,7,8,13),(3,4,9,14)])
   in(s1,map(m!!)permutation)
  v=fst(iterate roundOne(initial,message)!!7)
data Output=Output [Word32] [Word32] Word64 Word32 Word32
chaining(Output c m t len flags)=take 8(compress c m t len flags)
littleBytes w=[fromIntegral(w`shiftR`(8*i))|i<-[0..3]]
word b=BS.foldr(\x a->fromIntegral x+(a`shiftL`8))0 b
blockWords b=[word(BS.take 4(BS.drop(4*i)(b<>BS.replicate(64-BS.length b)0)))|i<-[0..15]]
chunks size b | BS.null b=[]
              | otherwise=BS.take size b:chunks size(BS.drop size b)
chunkOutput index b=go iv 0 blocks
 where
  blocks=if BS.null b then[BS.empty]else chunks 64 b
  go cv i [lastBlock]=Output cv(blockWords lastBlock)index(fromIntegral(BS.length lastBlock))(2 .|. if i==0 then 1 else 0)
  go cv i (a:rest)=go(take 8(compress cv(blockWords a)index 64(if i==0 then 1 else 0)))(i+1)rest
  go _ _ []=error "BLAKE3 final block missing"
rootDigest(Output c m _ len flags)=BS.pack(concatMap littleBytes(take 8(compress c m 0 len(flags .|.8))))
hash256 :: BS.ByteString -> Maybe BS.ByteString
hash256 b
 | BS.length b>2048=Nothing
 | BS.length b<=1024=Just(rootDigest(chunkOutput 0 b))
 | otherwise=Just(rootDigest(Output iv parentWords 0 64 4))
 where parentWords=chaining(chunkOutput 0(BS.take 1024 b))++chaining(chunkOutput 1(BS.drop 1024 b))
patternInput :: Int -> BS.ByteString
patternInput len=BS.pack[fromIntegral(i`mod`251)|i<-[0..len-1]]
