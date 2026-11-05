-- | Bounded BIP157/158 client reference. Hash names explicitly identify the
-- explorer/display boundary. Raw SHA256d digests are already wire bytes.
module JetDiscovery.Ref.CompactFilters
 (displayHashToRaw,rawHashToDisplay,sha256d,blockHashRaw,filterHeaderRaw
 ,hashToRange,encodeBasic,decodeBasic,constructBasic,matchBasic) where
import qualified Data.ByteString as B
import Data.Bits
import Data.List(sort,nub)
import qualified JetDiscovery.Ref.SipHash as Sip
import JetDiscovery.Tx(hex,unhex,hashToBytes,sha256)

m=784931
sha256d=hashToBytes.sha256.hashToBytes.sha256
displayHashToRaw text=let raw=unhex text in if B.length raw==32 then B.reverse raw else error "display hash must be32 bytes"
rawHashToDisplay raw|B.length raw==32=hex(B.reverse raw)
                    |otherwise=error "raw hash must be32 bytes"
blockHashRaw header|B.length header==80=sha256d header
                   |otherwise=error "block header must be80 bytes"
filterHeaderRaw serialized previousRaw
 |B.length previousRaw==32=sha256d(sha256d serialized<>previousRaw)
 |otherwise=error "previous filter header must be32 raw bytes"
little bytes=sum[toInteger b`shiftL`(8*i)|(i,b)<-zip[0..](B.unpack bytes)]
hashToRange rawBlockHash n item
 |B.length rawBlockHash/=32=error "block hash must be raw32 digest bytes"
 |n<0||n>16=error "bounded filter count0..16"
 |otherwise=(toInteger(Sip.sipHash24(fromInteger(little(B.take 8 rawBlockHash)))(fromInteger(little(B.take 8(B.drop 8 rawBlockHash))))item)*n*m)`shiftR`64
packBits bits=B.pack[fromInteger(sum[if b then 1`shiftL`(7-i)else 0|(i,b)<-zip[0..]chunk])|chunk<-chunks padded]
 where padded=bits++replicate((-length bits)`mod`8)False
       chunks []=[];chunks xs=take 8 xs:chunks(drop 8 xs)
encodeBasic values
 |length values>16||values/=sort values||any(<0)values||any(>=toInteger(length values)*m)values=error "bounded canonical basic filter values"
 |otherwise=B.singleton(fromIntegral(length values))<>packBits(concatMap encode(zipWith(-)values(0:values)))
 where encode delta=replicate(fromInteger(delta`shiftR`19))True++[False]++[testBit delta i|i<-[18,17..0]]
decodeBasic raw
 |B.null raw||B.head raw>16=Nothing
 |otherwise=do
   (values,_)<-readN n 0 bits
   if encodeBasic values==raw then Just values else Nothing
 where
  n=fromIntegral(B.head raw)
  bits=[testBit byte i|byte<-B.unpack(B.tail raw),i<-[7,6..0]]
  readN 0 _ rest=Just([],rest)
  readN count previous rest=do
   (q,after)<-unary 0 rest
   if length after<19 then Nothing else do
    let remainder=foldl(\a b->a*2+if b then 1 else 0)0(take 19 after)
        value=previous+(q`shiftL`19)+remainder
    if value>=toInteger n*m then Nothing else do
     (values,remaining)<-readN(count-1)value(drop 19 after)
     Just(value:values,remaining)
  unary _ []=Nothing
  unary q(False:rest)=Just(q,rest)
  unary q(True:rest)|q>=24=Nothing
                    |otherwise=unary(q+1)rest
constructBasic rawBlockHash items=let unique=nub items;n=toInteger(length unique)
                                 in encodeBasic(sort(map(hashToRange rawBlockHash n)unique))
matchBasic rawBlockHash serialized item=do
 values<-decodeBasic serialized
 let n=toInteger(length values)
 Just(n>0&&hashToRange rawBlockHash n item`elem`values)
