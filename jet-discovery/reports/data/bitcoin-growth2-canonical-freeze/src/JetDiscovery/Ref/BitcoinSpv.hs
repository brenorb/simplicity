-- | Byte-oriented bounded historical Bitcoin SPV receipt reference.
module JetDiscovery.Ref.BitcoinSpv
 ( Header,Payment,Proof,compactTarget,encodeCompact,headerBytes,headerHash,paymentBytes
 , verify,fixture,powLimit
 ) where
import qualified Data.ByteString as B
import Data.Bits (shiftL,shiftR,(.&.))
import Data.Serialize (runPut)
import JetDiscovery.Tx (unhex,putCompactSize)
import JetDiscovery.Ref.BitcoinGrowth (sha256d,le32,le64)
import qualified JetDiscovery.Ref.Bip340 as R

type Header=(Integer,(B.ByteString,(B.ByteString,(Integer,(Integer,Integer)))))
type Aff=(Integer,Integer)
type Payment=(((B.ByteString,Integer),B.ByteString),((Integer,Aff),(Integer,Aff)))
type Proof=((Header,(Header,Header)),(Payment,B.ByteString))
powLimit=0xffff `shiftL` 208

encodeCompact target
 | target<=0=0
 | otherwise=(toInteger finalSize `shiftL` 24)+finalMantissa
 where
  size=length(takeWhile(<=target)[256^i|i<-[0::Int ..]])
  mantissa=if size<=3 then target `shiftL` (8*(3-size)) else target `shiftR` (8*(size-3))
  (finalSize,finalMantissa)=if mantissa .&. 0x800000/=0 then(size+1,mantissa`shiftR`8)else(size,mantissa)
compactTarget bits
 | exponent<1||exponent>29||mantissa<=0||bits .&. 0x800000/=0=Nothing
 | target<=0||target>powLimit||encodeCompact target/=bits=Nothing
 | otherwise=Just target
 where
  exponent=fromInteger(bits`shiftR`24)
  mantissa=bits .&. 0x7fffff
  target=if exponent<=3 then mantissa`shiftR`(8*(3-exponent))else mantissa`shiftL`(8*(exponent-3))
headerBytes(v,(prev,(root,(time,(bits,nonce)))))=le32 v<>prev<>root<>le32 time<>le32 bits<>le32 nonce
headerHash=sha256d.headerBytes
paymentBytes(((prev,index),script),((a,(ax,ay)),(b,(bx,by))))=
 le32 1<>B.singleton 1<>prev<>le32 index<>runPut(putCompactSize(fromIntegral(B.length script)))<>script
 <>le32 0xffffffff<>B.singleton 2<>out a ax ay<>out b bx by<>le32 0
 where out value x y=le64 value<>unhex "434104"<>R.bytesFromInt x<>R.bytesFromInt y<>B.singleton 0xac
verify checkpoint trustedTip ((h0,(h1,h2)),(payment,sibling))=
 case compactTarget(bits h0) of
  Nothing->False
  Just target->headerHash h0==checkpoint&&headerHash h2==trustedTip
   &&prev h1==headerHash h0&&prev h2==headerHash h1
   &&bits h0==bits h1&&bits h1==bits h2
   &&all(\h->R.intFromBytes(B.reverse(headerHash h))<=target)[h0,h1,h2]
   &&sha256d(sibling<>sha256d(paymentBytes payment))==root h1
   &&B.length script<=511&&a>0&&point key
 where
  bits(_,(_,(_,(_, (b,_)))))=b
  prev(_, (p,_))=p
  root(_,(_, (r,_)))=r
  ((_,script),((a,key),_))=payment
  point(x,y)=x>=0&&x<R.p&&y>=0&&y<R.p&&(y*y-x*x*x-7)`mod`R.p==0

fixture :: IO Proof
fixture=do
 raw<-readFile "vendor-specs/bitcoin-growth/spv-receipt-fixture.tsv"
 let rows=map fields(drop 1(lines raw))
     field name=case[v|[k,v]<-rows,k==name]of[v]->v;_->error("SPV fixture field "++name)
     bytes=unhex.field
     number=read.field
     scalar=R.intFromBytes.bytes
     le b=R.intFromBytes(B.reverse b)
     header key=let b=bytes key in (le(B.take 4 b),(B.take 32(B.drop 4 b),(B.take 32(B.drop 36 b),
       (le(B.take 4(B.drop 68 b)),(le(B.take 4(B.drop 72 b)),le(B.drop 76 b))))))
     payment=(((bytes "previous_hash_raw",number "previous_index"),bytes "script_sig"),
       ((number "value0",(scalar "key0x",scalar "key0y")),(number "value1",(scalar "key1x",scalar "key1y"))))
 if paymentBytes payment/=bytes "payment_raw" then error "SPV payment serializer disagrees with original bytes"
 else return((header "header0",(header "header1",header "header2")),(payment,bytes "coinbase_txid_raw"))
 where fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
