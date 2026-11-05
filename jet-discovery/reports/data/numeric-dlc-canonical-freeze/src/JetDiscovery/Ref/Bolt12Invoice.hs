-- | Independent byte-oriented BOLT12 canonical TLV and invoice transcript.
-- BOLTs191462825ae341f0a27098765c075f01ca9bc6c2, CC-BY4.0.
module JetDiscovery.Ref.Bolt12Invoice
 (bigSize,tlv,parseTlv,merkle,signatureMessage,invoiceFields,invoiceRaw
 ,requestFields,pathBytes,nodeSecret,nodeKey,payerKey,firstTlv,verifyProfile) where
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import qualified Data.List as L
import Data.Bits(shiftR,(.&.))
import JetDiscovery.Tx(sha256,hashToBytes,unhex)
import qualified JetDiscovery.Ref.Bip340 as R
import JetDiscovery.Ref.SilentPayment(compressed)
bigSize x|x<0=error "negative bigsize"
 |x<253=B.singleton(fromInteger x)
 |x<65536=B.singleton 253<>be 2 x
 |x<4294967296=B.singleton 254<>be 4 x
 |x<18446744073709551616=B.singleton 255<>be 8 x
 |otherwise=error "bigsize overflow"
be width x=B.pack[fromInteger(x`shiftR`(8*i))|i<-[width-1,width-2..0]]
tlv(typ,body)=bigSize typ<>bigSize(toInteger(B.length body))<>body
parseTlv raw=loop(-1)raw
 where
  number b|B.null b=Left "truncated bigsize"
          |B.head b<253=Right(toInteger(B.head b),B.tail b)
          |otherwise=let width=case B.head b of 253->2;254->4;_->8
                         minimum=case width of 2->253;4->65536;_->4294967296
                         x=R.intFromBytes(B.take width(B.tail b))
                     in if B.length b<width+1||x<minimum then Left "noncanonical/truncated bigsize"else Right(x,B.drop(width+1)b)
  loop _ b|B.null b=Right[]
  loop previous b=do
   (typ,rest)<-number b
   (size,body)<-number rest
   if typ<=previous||size>toInteger(B.length body)then Left "unordered/duplicate/truncated TLV"else do
    next<-loop typ(B.drop(fromInteger size)body)
    return((typ,B.take(fromInteger size)body):next)
hash tag bytes=let h=hashToBytes(sha256 tag)in hashToBytes(sha256(h<>h<>bytes))
branch a b=hash(C.pack "LnBranch")(min a b<>max a b)
merkle fields
 |null unsigned=error "BOLT12 empty signed stream"
 |otherwise=tree[branch(hash(C.pack "LnLeaf")(tlv f))(hash(C.pack "LnNonce"<>first)(bigSize typ))|f@(typ,_)<-unsigned]
 where
  unsigned=filter(\(typ,_)->typ<240||typ>1000)(L.sortOn fst fields)
  first=tlv(head unsigned)
  tree[a]=a
  tree xs=let cut=last(takeWhile(<length xs)(iterate(*2)1));(left,right)=splitAt cut xs
          in branch(tree left)(tree right)
signatureMessage name fields=R.taggedHash("lightning"++name++"signature")(merkle fields)

-- This complete reader profile commits the request, node identity, one route
-- and the transport/reply-path context. The test path bytes are from the
-- published payer-proof invoice fixture; encrypted recipient data is opaque
-- to invoice readers, not claimed to be an end-to-end paid Lightning route.
nodeSecret=R.intFromBytes(B.replicate 32 0x46)
nodeKey=compressed(R.pointMul R.gPt nodeSecret)
payerKey=compressed(R.pointMul R.gPt(R.intFromBytes(B.replicate 32 0x42)))
requestFields=[(0,B.replicate 16 0),(10,C.pack "Bounded invoice"),(22,nodeKey),(82,be 2 1000),(88,payerKey),(99,B.singleton 0x42)]
firstTlv=tlv(head requestFields)
pathBytes hops=unhex "027f31ebc5462c1fdce1b737ecff52d37d75dea43ce11c74d25aa297165faa2007032c0b7cf95324a07d05398b240174dc0c2be444d96b159aa6c7f7b1e668680991"
 <>B.singleton(fromInteger hops)<>unhex "02edabbd16b41c8371b92ef2f04c1185b4f03b6dcd52ba9b78d9d7c89c8f221145001000000000000000000000000000000000"
invoiceFields created expiry paymentHash amount maximum features hops=requestFields++
 [(160,pathBytes hops),(162,be 4 1<>be 4 2<>be 2 3<>be 8 4<>be 8 maximum<>be 2 0),
  (164,be 4 created),(166,be 2 expiry),(168,paymentHash),(170,be 2 amount),(174,be 1 features),(176,nodeKey),(3000000001,B.singleton 0x42)]
invoiceRaw fields signature=B.concat(map tlv(L.sortOn fst((240,signature):fields)))
verifyProfile now raw=case parseTlv raw of
 Left _->False
 Right fields->case mapM(\typ->lookup typ fields)[164,166,168,170,162,174,240]of
  Just[createdBytes,expiryBytes,paymentHash,amountBytes,payinfo,featureBytes,signature]
   |map B.length[createdBytes,expiryBytes,paymentHash,amountBytes,payinfo,featureBytes,signature]==[4,2,32,2,28,1,64]->
    let created=R.intFromBytes createdBytes;expiry=R.intFromBytes expiryBytes
        amount=R.intFromBytes amountBytes;maximum=R.intFromBytes(B.take 8(B.drop 18 payinfo))
        features=R.intFromBytes featureBytes
        actual=invoiceFields created expiry paymentHash amount maximum features 1
    in created>=2^24&&expiry>=256&&created<=now&&now<=created+expiry&&amount==1000
      &&maximum>=amount&&features>0&&features.&.0x55==0
      &&raw==invoiceRaw actual signature
      &&R.verify(B.tail nodeKey)(signatureMessage "invoice" actual)signature
  _->False
