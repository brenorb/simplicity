{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Complete supported BOLT12 client invoice reader, not an onchain clock.
-- Exact primary TLV/nonce/Merkle/signature specification and client boundaries
-- are retained in reports/BITCOIN-GROWTH2.md. One structured proof witness.
module JetDiscovery.Lib.Bolt12Invoice(entry,Proof,Fields,invoiceKernel,invoiceProof,merkleKernel) where
import Prelude hiding(drop,take,not,and,or,maximum)
import qualified Prelude as P
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as S
import Simplicity.Bitcoin.Term(Simplicity,Primitive)
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer(ctxWith)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.Bolt12Invoice as Ref

type Sig=(Word256,Word256)
type Fields=(Word32,(Word16,(Word256,(Word16,(Word64,(Word8,Word8))))))
type Proof=(Buffer511 Word8,(Fields,Sig))
same :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a ()
same a b=(a&&&b)>>>eq>>>verify
appendConst :: Assert t => B.ByteString -> t Ctx8 Ctx8
appendConst bytes|B.null bytes=iden
 |otherwise=piece n(B.take n bytes)>>>appendConst(B.drop n bytes)
 where
  n=P.head[k|k<-[32,16,8,4,2,1],k<=B.length bytes]
  piece 32 b=ctxWith(konst(w256FromBytes b))ctx8Add32
  piece 16 b=ctxWith(konst(toWord128(R.intFromBytes b)))ctx8Add16
  piece 8 b=ctxWith(konst(w64(R.intFromBytes b)))ctx8Add8
  piece 4 b=ctxWith(konst(w32(R.intFromBytes b)))ctx8Add4
  piece 2 b=ctxWith(konst(w16(R.intFromBytes b)))ctx8Add2
  piece _ b=ctxWith(konst(w8(R.intFromBytes b)))ctx8Add1
start :: (Assert t,TyC a) => String -> t a(a,Ctx8)
start tag=iden&&&(unit>>>ctx8InitTag tag)
append :: (Assert t,TyC a,TyC b) => t a b -> t(Ctx8,b)Ctx8 -> t(a,Ctx8)(a,Ctx8)
append f jet=oh&&&((ih&&&(oh>>>f))>>>jet)
constant :: (Assert t,TyC a) => B.ByteString -> t(a,Ctx8)(a,Ctx8)
constant bytes=oh&&&(ih>>>appendConst bytes)
created :: Core t => t Fields Word32
created=oh
expiry :: Core t => t Fields Word16
expiry=ioh
paymentHash :: Core t => t Fields Word256
paymentHash=iioh
amount :: Core t => t Fields Word16
amount=ih>>>ih>>>ih>>>oh
maximum :: Core t => t Fields Word64
maximum=ih>>>ih>>>ih>>>ih>>>oh
features :: Core t => t Fields Word8
features=ih>>>ih>>>ih>>>ih>>>ih>>>oh
hops :: Core t => t Fields Word8
hops=ih>>>ih>>>ih>>>ih>>>ih>>>ih
fieldTypes=[0,10,22,82,88,99,160,162,164,166,168,170,174,176,3000000001]::[Integer]
fieldStep :: forall t. Assert t => Integer -> t(Fields,Ctx8)(Fields,Ctx8)
fieldStep typ=case typ of
 160->constant(unhex "a076"<>B.take 66(Ref.pathBytes 1))>>>append hops ctx8Add1>>>constant(B.drop 67(Ref.pathBytes 1))
 162->constant(unhex "a21c000000010000000200030000000000000004")>>>append maximum ctx8Add8>>>constant(unhex "0000")
 164->constant(unhex "a404")>>>append created ctx8Add4
 166->constant(unhex "a602")>>>append expiry ctx8Add2
 168->constant(unhex "a820")>>>append paymentHash ctx8Add32
 170->constant(unhex "aa02")>>>append amount ctx8Add2
 174->constant(unhex "ae01")>>>append features ctx8Add1
 176->constant(Ref.tlv(176,Ref.nodeKey))
 3000000001->constant(Ref.tlv(3000000001,B.singleton 0x42))
 _->case lookup typ Ref.requestFields of Just body->constant(Ref.tlv(typ,body));_->error "unsupported BOLT12 field"
leaf :: Assert t => Integer -> t Fields Word256
leaf typ=start "LnLeaf">>>fieldStep typ>>>ih>>>ctx8Finalize
nonce typ=let tag=B.pack(map(fromIntegral.fromEnum)"LnNonce")<>Ref.firstTlv
              h=hashToBytes(sha256 tag)
          in w256FromBytes(hashToBytes(sha256(h<>h<>Ref.bigSize typ)))
branch :: Assert t => t(Word256,Word256)Word256
branch=(((oh&&&ih)>>>A.le word256)&&&iden>>>cond iden(ih&&&oh))
 >>>start "LnBranch">>>append oh ctx8Add32>>>append ih ctx8Add32>>>ih>>>ctx8Finalize
merkleKernel :: forall t. Assert t => t Fields Word256
merkleKernel=tree paired
 where
  node :: t(Word256,Word256)Word256
  node=branch
  paired :: [t Fields Word256]
  paired=[(leaf typ&&&konst(nonce typ))>>>node|typ<-fieldTypes]
  tree :: [t Fields Word256] -> t Fields Word256
  tree[x]=x
  tree xs=let cut=P.last(P.takeWhile(<P.length xs)(P.iterate(*2)1));(left,right)=P.splitAt cut xs
          in(tree left&&&tree right)>>>node
signatureMessage :: Assert t => t Fields Word256
signatureMessage=merkleKernel>>>((unit>>>ctx8InitTag "lightninginvoicesignature")&&&iden)>>>ctx8Add32>>>ctx8Finalize
wireHash :: forall t. Assert t => t(Fields,Sig)Word256
wireHash=(iden&&&(unit>>>ctx8Init))>>>L.foldr(>>>)iden[step typ|typ<-P.init fieldTypes]
 >>>constant(unhex "f040")>>>append ioh ctx8Add32>>>append iih ctx8Add32
 >>>step 3000000001>>>ih>>>ctx8Finalize
 where
  step :: Integer -> t((Fields,Sig),Ctx8)((Fields,Sig),Ctx8)
  step typ=oh&&&((ooh&&&ih)>>>fieldStep typ>>>ih)
widen32 :: Core t => t Word32 Word64
widen32=konst(w32 0)&&&iden
widen16 :: Core t => t Word16 Word64
widen16=konst(w32 0)&&&(konst(w16 0)&&&iden)
policy :: forall t. Assert t => Integer -> t Fields()
policy now=(time&&&same amount(konst(w16 1000))&&&range&&&same hops(konst(w8 1))&&&featureRules)>>>unit
 where
  time :: t Fields()
  time=(((konst(w32(2^24))&&&created)>>>A.le word32>>>verify)
   &&&((konst(w16 256)&&&expiry)>>>A.le word16>>>verify)
   &&&(((created>>>widen32)&&&konst(w64 now))>>>A.le word64>>>verify)
   &&&((konst(w64 now)&&&(((created>>>widen32)&&&(expiry>>>widen16))>>>A.add word64>>>ih))>>>A.le word64>>>verify))>>>unit
  range :: t Fields()
  range=((amount>>>widen16)&&&maximum)>>>A.le word64>>>verify
  featureRules :: t Fields()
  featureRules=(same((features&&&konst(w8 0x55))>>>W.bitwise_and word8)(konst(w8 0))
    &&&((konst(w8 0)&&&features)>>>A.lt word8>>>verify))>>>unit
invoiceProof :: (Simplicity t,Primitive t) => Integer -> Proof -> t()()
invoiceProof now proof=witness proof>>>invoiceKernel now
invoiceKernel :: (Assert t,Primitive t) => Integer -> t Proof()
invoiceKernel now=((oh>>>sha256Buffer511)&&&ih)
 >>>((same oh(ih>>>wireHash)&&&iden)>>>ih)>>>ih
 >>>(((oh>>>policy now)&&&(((konst(w256FromBytes(B.tail Ref.nodeKey))&&&(oh>>>signatureMessage))&&&ih)>>>S.bip_0340_verify))>>>unit)

fieldsW c e h a mx f hop=(w32 c,(w16 e,(w256FromBytes h,(w16 a,(w64 mx,(w8 f,w8 hop))))))
sigW raw=(w256FromBytes(B.take 32 raw),w256FromBytes(B.drop 32 raw))
entry :: IO Entry
entry=return(Entry "app-bolt12-invoice-authorization"
 "Complete supported BOLT12 invoice client reader: canonical raw TLVs, exact Merkle signature, request/amount/path/features and UTC policy"
 "BOLT12/BOLT4 revision191462825ae341f0a27098765c075f01ca9bc6c2; official all97row inventory plus4signaturecore/5fullinvoice transcripts"
 BitcoinApp(Derived "Full bounded raw invoice profile, signed by published testmerchant key; actual malformed invoices re-signed to isolate policy checks; complete official transcript cores separately checked")
 ["CLIENT MODE: trusted client supplies actual canonical raw invoice TLVs, its stored request/reply-path context and current UTC time1700000600; no onchain clock or nLockTime freshness claim",
  "Known requested offer/metadata/payer/amount fields, including unknown odd type99, must copy exactly; expected merchant node identity is committed and reply transport authentication is external client state",
  "One committed one-hop route with canonical compressed public points and opaque16-byte encrypted recipient data; one exact payinfo/empty allowedfeatures; final-hop decryption/routing/payment execution is not invoice-reader work and not claimed",
  "Exact canonical TLV bytes reconstructed and SHA256-bound to raw<=511byte invoice including signature and unknown high type3000000001; unsupported fields/profiles rejected, no field silently dropped",
  "Exact LnLeaf, binary LnNonce||firstTLV tags, sorted LnBranch and uneven tree; merchant BIP340 invoice signature includes all non-signature fields, including unknown fields",
  "Fixed requested1000msat, amount within path min/max, nonzero hop count, minimal1byte invoicefeatures; unknown odd bits ignored, unknown even bits rejected; one-part payment only",
  "Timestamp32/expiry16 must have minimal4/2byte truncated encodings; checked UTC expiry plus conservative no-future-creation client policy; known fixture request metadata/route are testdata, not production entropy or proof of route viability",
  "Bech32-style ASCII decoding, external reply-path identity, remembered request and UTC acquisition are trusted client boundaries; no paid receipt/preimage knowledge or Bitcoin chain membership claim",
  "All97 official BOLT12 JSON rows inventoried;4Merkle/signature cores and5published raw invoice signatures separately checked, other offer/string/payer-proof cases are outside this bounded complete invoice application",
  "Native primitive environment is unused; transaction budget comparisons do not imply enforceability as a Bitcoin spend"]
 (boundProgram(invoiceKernel now))vectors)
 where
  now=1700000600;h=hashToBytes(sha256(B.replicate 32 1))
  env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)100000(BL.fromStrict(unhex "51"))0xffffffff][mkOutput 99000(unhex "51")]0)0 defaultTap
  make c e hash a mx f hop=
   let fs=Ref.invoiceFields c e hash a mx f hop
       sig=R.sign Ref.nodeSecret(Ref.signatureMessage "invoice" fs)(B.replicate 32 0)
   in(buffer511FromBytes(Ref.invoiceRaw fs sig),(fieldsW c e hash a mx f hop,sigW sig))
  good=make 1700000000 3600 h 1000 1000000 2 1
  boundary=make 1700000000 600 h 1000 1000000 2 1
  (_,(_,signature))=good
  malformed alter=
   let fs=alter(Ref.invoiceFields 1700000000 3600 h 1000 1000000 2 1)
       s=R.sign Ref.nodeSecret(Ref.signatureMessage "invoice" fs)(B.replicate 32 0)
   in(buffer511FromBytes(Ref.invoiceRaw fs s),(fieldsW 1700000000 3600 h 1000 1000000 2 1,sigW s))
  corrupt=let(r,s)=signature;bad=(r,w256 1);fs=Ref.invoiceFields 1700000000 3600 h 1000 1000000 2 1
          in(buffer511FromBytes(Ref.invoiceRaw fs(w256ToBytes r<>w256ToBytes(w256 1))),(fieldsW 1700000000 3600 h 1000 1000000 2 1,bad))
  vectors=[Vector "complete authenticated invoice with unknown odd fields" env good Accept,
   Vector "current UTC equals exact expiration boundary" env boundary Accept,
   Vector "fresh valid merchant signature cannot change requested amount" env(make 1700000000 3600 h 1001 1000000 2 1)Reject,
   Vector "fresh valid merchant signature cannot authorize expired invoice" env(make 1699990000 3600 h 1000 1000000 2 1)Reject,
   Vector "future creation time violates explicit client policy" env(make 1700000700 3600 h 1000 1000000 2 1)Reject,
   Vector "unknown even feature freshly signed" env(make 1700000000 3600 h 1000 1000000 1 1)Reject,
   Vector "nonminimal zero feature byte freshly signed" env(make 1700000000 3600 h 1000 1000000 0 1)Reject,
   Vector "zero-hop path freshly signed" env(make 1700000000 3600 h 1000 1000000 2 0)Reject,
   Vector "path max_htlc below authorized amount freshly signed" env(make 1700000000 3600 h 1000 999 2 1)Reject,
   Vector "nonminimal two-byte expiry freshly signed" env(make 1700000000 1 h 1000 1000000 2 1)Reject,
   Vector "changed copied unknown request field freshly signed" env(malformed(map(\(t,b)->(t,if t==99 then B.singleton 0x43 else b))))Reject,
   Vector "missing mandatory payment_hash freshly signed" env(malformed(filter((/=168).fst)))Reject,
   Vector "duplicate known TLV freshly signed" env(malformed(\fs->head fs:fs))Reject,
   Vector "raw invoice contains actual invalid signature" env corrupt Reject]
