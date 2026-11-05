{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Bounded BIP352 covenant with authenticated input provenance and exact
-- BIP374 v0.3.1 ECDH proof. All logical fields enter through one witness.
module JetDiscovery.Lib.SilentPayment(entry,silent,silentKernel,Proof,deriveOutput,dleq374) where
import Prelude hiding(drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.List as L
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as S
import Simplicity.Bitcoin.Term(Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import Simplicity.Bitcoin.DataTypes(SigTx(..),SigTxInput(..),Outpoint(..),TapEnv(..))
import Simplicity.LibSecp256k1.Schnorr(PubKey(..))
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer(ctxWith)
import qualified JetDiscovery.Lib.Ripemd160 as RI
import JetDiscovery.Corpus.Apps(sigMsg)
import JetDiscovery.Tx
import JetDiscovery.Types
import JetDiscovery.Run(progCmr)
import JetDiscovery.Lib.BitcoinFunding(fundingScript,fundingSecret)
import qualified Data.ByteString as B
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.SilentPayment as Ref
import qualified JetDiscovery.Ref.BitcoinGrowth as Wire

type GE=(Word256,Word256)
type CKey=(Word8,Word256)
type DER70=(Word512,(Word32,Word16))
type Proof=((Word256,CKey),(DER70,(GE,(Word256,Word256))))
type Dleq=((GE,(GE,GE)),((Word256,Word256),Word256))
type Challenge=(GE,(GE,(GE,(GE,(GE,Word256)))))
type Derivation=(GE,((Word256,Word32),GE))

same :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a ()
same a b=(a&&&b)>>>eq>>>verify
start :: (Assert t,TyC a) => String -> t a(a,Ctx8)
start tag=iden&&&(unit>>>if null tag then ctx8Init else ctx8InitTag tag)
append :: (Assert t,TyC a,TyC b) => t a b -> t(Ctx8,b)Ctx8 -> t(a,Ctx8)(a,Ctx8)
append f jet=oh&&&((ih&&&(oh>>>f))>>>jet)
field :: Assert t => t Word256()
field=(iden&&&konst(w256 R.p))>>>A.lt word256>>>verify
scalar :: Assert t => t Word256()
scalar=(iden&&&konst(w256 R.n))>>>A.lt word256>>>verify
nonzeroScalar :: Assert t => t Word256 Word256
nonzeroScalar=(((scalar&&&((iden&&&konst(w256 0))>>>eq>>>not iden>>>verify))>>>unit)&&&iden)>>>ih
point :: Assert t => t GE()
point=((oh>>>field)&&&(ih>>>field)&&&(S.ge_is_on_curve>>>verify))>>>unit
toJ :: (Core t,TyC a) => t a GE -> t a(GE,Word256)
toJ p=p&&&konst(w256 1)
normalize :: Assert t => t(GE,Word256)GE
normalize=S.gej_normalize>>>verify
liftX :: Assert t => t Word256 GE
liftX=(field&&&iden)>>>ih>>>(false&&&iden)>>>S.decompress>>>verify
decompress :: Assert t => t CKey GE
decompress=(((((or ((oh&&&konst(w8 2))>>>eq)((oh&&&konst(w8 3))>>>eq))>>>verify)
 &&&(ih>>>field))>>>unit)&&&iden)>>>ih
 >>>(((oh&&&konst(w8 3))>>>eq)&&&ih)>>>S.decompress>>>verify
prefix :: Assert t => t GE Word8
prefix=(ih>>>S.fe_is_odd)&&&unit>>>cond(konst(w8 3))(konst(w8 2))
appendPoint :: (Assert t,TyC a) => t a GE -> t(a,Ctx8)(a,Ctx8)
appendPoint p=append(p>>>prefix)ctx8Add1>>>append(p>>>oh)ctx8Add32

challenge374 :: forall t. Assert t => t Challenge Word256
challenge374=start "BIP0374/challenge">>>appendPoint a>>>appendPoint b>>>appendPoint c
 >>>append(konst(w8 2))ctx8Add1>>>append(konst(w256(R.xOnly R.gPt)))ctx8Add32
 >>>appendPoint r1>>>appendPoint r2>>>append msg ctx8Add32>>>ih>>>ctx8Finalize>>>S.scalar_normalize
 where
  a :: t Challenge GE
  a=oh
  b :: t Challenge GE
  b=ioh
  c :: t Challenge GE
  c=iioh
  r1 :: t Challenge GE
  r1=ih>>>ih>>>ih>>>oh
  r2 :: t Challenge GE
  r2=ih>>>ih>>>ih>>>ih>>>oh
  msg :: t Challenge Word256
  msg=ih>>>ih>>>ih>>>ih>>>ih

dleq374 :: forall t. Assert t => t Dleq()
dleq374=(canonical&&&same challenge e)>>>unit
 where
  a :: t Dleq GE
  a=ooh
  b :: t Dleq GE
  b=oh>>>ih>>>oh
  c :: t Dleq GE
  c=oh>>>ih>>>ih
  e :: t Dleq Word256
  e=ih>>>oh>>>oh
  s :: t Dleq Word256
  s=ih>>>oh>>>ih
  msg :: t Dleq Word256
  msg=ih>>>ih
  r1 :: t Dleq GE
  r1=(((e>>>S.scalar_negate)&&&toJ a)&&&s)>>>S.linear_combination_1>>>normalize
  r2 :: t Dleq GE
  r2=((s&&&toJ b)>>>S.scale)&&&(((e>>>S.scalar_negate)&&&toJ c)>>>S.scale)>>>S.gej_add>>>normalize
  canonical :: t Dleq()
  canonical=((a>>>point)&&&(b>>>point)&&&(c>>>point)&&&(e>>>scalar)&&&(s>>>scalar))>>>unit
  challenge :: t Dleq Word256
  challenge=(a&&&(b&&&(c&&&(r1&&&(r2&&&msg)))))>>>challenge374

inputHash :: Assert t => t(GE,(Word256,Word32))Word256
inputHash=start "BIP0352/Inputs">>>append ioh ctx8Add32>>>append iih ctxAddLE32
 >>>appendPoint oh>>>ih>>>ctx8Finalize>>>nonzeroScalar
sharedTweak :: Assert t => t GE Word256
sharedTweak=start "BIP0352/SharedSecret">>>appendPoint iden>>>append(konst(w32 0))ctx8Add4
 >>>ih>>>ctx8Finalize>>>nonzeroScalar
deriveOutput :: forall t. Assert t => GE -> t Derivation Word256
deriveOutput spend=((konst spend>>>point)&&&output)>>>ih
 where
  h :: t Derivation Word256
  h=(oh&&&ioh)>>>inputHash
  shared :: t Derivation GE
  shared=(h&&&toJ iih)>>>S.scale>>>normalize
  tweak :: t Derivation Word256
  tweak=shared>>>sharedTweak
  output :: t Derivation Word256
  output=(((konst(w256 1))&&&toJ(konst spend))&&&tweak)>>>S.linear_combination_1>>>normalize>>>oh

-- Actual P2PKH key provenance: RIPEMD160(SHA256(compressed public key)),
-- serialized in the exact 25-byte locking script, then SHA256 for the primitive.
p2pkhHash :: forall t. Assert t => t CKey Word256
p2pkhHash=(((unit>>>ctx8Init)&&&oh)>>>ctx8Add1)&&&ih>>>ctx8Add32>>>ctx8Finalize
 >>>((RI.ivT&&&block)>>>RI.ripemd160Compress)>>>script
 where
  word :: Int -> t Word256 Word32
  word i=RI.pick(i>=4)(RI.pick(odd(i`div`2))(RI.pick(odd i)iden))>>>bswap32
  block :: t Word256(Vector16 Word32)
  block=RI.mk16([word i|i<-[0..7]]++[konst(w32 0x80)]++replicate 5(konst(w32 0))++[konst(w32 256),konst(w32 0)])
  script :: t RI.W5 Word256
  script=(iden&&&(unit>>>ctx8Init>>>ctxWith(konst(w8 0x76))ctx8Add1>>>ctxWith(konst(w16 0xa914))ctx8Add2))
   >>>append oh ctxAddLE32>>>append ioh ctxAddLE32>>>append iioh ctxAddLE32
   >>>append (ih>>>ih>>>ih>>>oh)ctxAddLE32>>>append (ih>>>ih>>>ih>>>ih)ctxAddLE32
   >>>ih>>>ctxWith(konst(w16 0x88ac))ctx8Add2>>>ctx8Finalize
scriptSigHash :: Assert t => t(DER70,CKey)Word256
scriptSigHash=(iden&&&(unit>>>ctx8Init>>>ctxWith(konst(w8 71))ctx8Add1))
 >>>append (oh>>>oh)ctx8Add64>>>append (oh>>>ioh)ctx8Add4>>>append (oh>>>iih)ctx8Add2
 >>>append (konst(w16 0x0121))ctx8Add2>>>append ioh ctx8Add1>>>append iih ctx8Add32>>>ih>>>ctx8Finalize
p2trHash :: Assert t => t Word256 Word256
p2trHash=(((unit>>>ctx8Init)&&&konst(w16 0x5120)>>>ctx8Add2)&&&iden)>>>ctx8Add32>>>ctx8Finalize
bswap128 :: Core t => t Word128 Word128
bswap128=(ih>>>bswap64)&&&(oh>>>bswap64)
bswap256 :: Core t => t Word256 Word256
bswap256=(ih>>>bswap128)&&&(oh>>>bswap128)

silent :: (Simplicity t,Primitive t) => GE -> GE -> Proof -> t()()
silent scan spend proof=witness proof>>>silentKernel scan spend
silentKernel :: forall t. (Assert t,Primitive t) => GE -> GE -> t Proof()
silentKernel scan spend=(provenance&&&proof&&&native)>>>unit
 where
  pk0 :: t Proof Word256
  pk0=ooh
  pk1 :: t Proof CKey
  pk1=oih
  der :: t Proof DER70
  der=ioh
  c :: t Proof GE
  c=ih>>>ih>>>oh
  es :: t Proof(Word256,Word256)
  es=ih>>>ih>>>ih
  aggregate :: t Proof GE
  aggregate=(toJ(pk0>>>liftX)&&&(pk1>>>decompress))>>>S.gej_ge_add>>>normalize
  outpoint :: Int -> t Proof(Word256,Word32)
  outpoint i=konst(w32(toInteger i))>>>primitive Prim.InputPrevOutpoint>>>verify
  wire :: Int -> t Proof(Word256,Word32)
  wire i=(outpoint i>>>oh>>>bswap256)&&&(outpoint i>>>ih)
  smallest :: t Proof(Word256,Word32)
  smallest=choose&&&iden>>>cond(wire 0)(wire 1)
   where
    equalHash=((wire 0>>>oh)&&&(wire 1>>>oh))>>>eq
    hashLess=((wire 0>>>oh)&&&(wire 1>>>oh))>>>A.lt word256
    indexLess=((wire 0>>>ih>>>bswap32)&&&(wire 1>>>ih>>>bswap32))>>>A.lt word32
    choose=or hashLess(and equalHash indexLess)
  proof :: t Proof()
  proof=((aggregate&&&(konst scan&&&c))&&&(es&&&(unit>>>SigHash.sigAllHash)))>>>dleq374
  provenance :: t Proof()
  provenance=(same(unit>>>Tx.numInputs)(konst(w32 2))
   &&&same(unit>>>primitive Prim.CurrentIndex)(konst(w32 0))
   &&&((unit>>>primitive Prim.InternalKey)&&&konst(w256 R.nums)>>>eq>>>not iden>>>verify)
   &&&same(konst(w32 0)>>>primitive Prim.InputScriptHash>>>verify)(pk0>>>p2trHash)
   &&&same(konst(w32 0)>>>primitive Prim.InputScriptSigHash>>>verify)(konst(w256FromBytes(hashToBytes(sha256 B.empty))))
   &&&same(konst(w32 1)>>>primitive Prim.InputScriptHash>>>verify)(pk1>>>p2pkhHash)
   &&&same(konst(w32 1)>>>primitive Prim.InputScriptSigHash>>>verify)((der&&&pk1)>>>scriptSigHash)
   &&&((outpoint 0&&&outpoint 1)>>>eq>>>not iden>>>verify))>>>unit
  outputKey :: t Proof Word256
  outputKey=(aggregate&&&(smallest&&&c))>>>deriveOutput spend
  checkedAdd :: t Proof Word64 -> t Proof Word64 -> t Proof Word64
  checkedAdd a b=(a&&&b)>>>A.add word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
  total :: t Proof Word64
  total=checkedAdd(konst(w32 0)>>>primitive Prim.InputValue>>>verify)(konst(w32 1)>>>primitive Prim.InputValue>>>verify)
  native :: t Proof()
  native=(same(unit>>>Tx.numOutputs)(konst(w32 1))
   &&&same(konst(w32 0)>>>primitive Prim.OutputScriptHash>>>verify)(outputKey>>>p2trHash)
   &&&same total(checkedAdd(konst(w32 0)>>>primitive Prim.OutputValue>>>verify)(konst(w64 1000))))>>>unit

pointW :: R.Pt -> GE
pointW(Just(x,y))=(w256 x,w256 y)
pointW Nothing=error "infinite public point"
derW :: B.ByteString -> DER70
derW raw|B.length raw/=70=error "DER70 field bound"
        |otherwise=((w256FromBytes(B.take 32 raw),w256FromBytes(B.take 32(B.drop 32 raw))),
          (w32(R.intFromBytes(B.take 4(B.drop 64 raw))),w16(R.intFromBytes(B.drop 68 raw))))

entry :: IO Entry
entry=return(Entry "app-silent-payment-output-covenant"
 "BIP352 mixed-input silent-payment covenant with authenticated keys, real HASH160 and BIP374 ECDH proof"
 "BIP352 and BIP374 v0.3.1; pinned vendor-specs/bitcoin-growth/bip-0352.mediawiki and bip-0374.mediawiki"
 BitcoinApp(Derived "Real Taproot output-key setup, valid low-S legacy ECDSA input signature and exact BIP374 proof on actual sig_all_hash; BIP352 core separately tested against all3 compatible upstream cases")
 ["Exactly two eligible inputs: current P2TR scriptpath input0 with actual InternalKey != BIP341 NUMS H, and canonical compressed-P2PKH input1",
  "P2TR key binds actual InputScriptHash; P2PKH compressed key binds actual InputScriptHash via full HASH160 and exact two-push InputScriptSigHash; scriptSig contains canonical DER70 plus SIGHASH_ALL",
  "Bitcoin consensus validates the legacy ECDSA signature/DER and current Taproot control block; this program authenticates every byte needed for BIP352 public-key extraction",
  "No unavailable other-input Taproot witness metadata is trusted: other-P2TR, P2WPKH and P2SH-P2WPKH inputs are outside this bounded covenant",
  "One committed recipient, no labels or group sweeps, k=0; complete two-key aggregation, byte-lexicographic smallest wire outpoint, exact tagged hashes, scalar rejection, shared-secret weighting and P2TR output derivation",
  "ECDH C=a*B_scan is authenticated by exact BIP374 compressed-point transcript with optional message equal to actual native sig_all_hash; sender secrets are never witnesses",
  "This enforces the chosen Simplicity leaf or signer/output-validation policy, not an inescapable Taproot covenant: BIP352 senders know the current output private key and can choose a keypath spend",
  "Exactly one output consumes both input amounts minus1000 satoshis; derived tests include a same-txid outpoint1/256 ordering boundary and freshly proved wrong payouts",
  "All29 upstream vector groups /59 role cases are inventoried; all3 compatible sender core cases are tested separately, not claimed as full native-transaction vectors"]
 (boundProgram(silentKernel scanW spendW))vectors)
 where
  scan=R.pointMul R.gPt 23;spend=R.pointMul R.gPt 47
  scanW=pointW scan;spendW=pointW spend
  internal=17;legacy=22
  tap root=(defaultTap root){tapInternalKey=PubKey(fromInteger(R.pubkeyOf internal))}
  dummy :: Proof
  dummy=((w256 0,(w8 2,w256(R.xOnly R.gPt))),(((w256 0,w256 0),(w32 0,w16 0)),(pointW R.gPt,(w256 0,w256 0))))
  cmr=progCmr(Prog(silent scanW spendW dummy))
  outputSecret=case fundingSecret internal(tap cmr)of Just s->s;_->error "silent-payment Taproot setup"
  legacyPoint=R.pointMul R.gPt legacy
  legacyScript=Ref.p2pkhScript legacyPoint
  wire(Outpoint h i)=B.reverse(hashToBytes h)<>Wire.le32(toInteger i)
  p2tr x=unhex "5120"<>R.bytesFromInt x
  make op0 op1 override payout=
   let outpoints=[wire op0,wire op1]
       (derived,_,_)=Ref.derive outputSecret legacy outpoints scan spend
       destination=case override of Nothing->derived;Just x->x
       unsigned=mkTx 2[mkInput op0 60000(BL.fromStrict(fundingScript(tap cmr)))0xfffffffe,
         mkInput op1 40000(BL.fromStrict legacyScript)0xfffffffe][mkOutput payout(p2tr destination)]0
       der=Ref.ecdsaDER70 legacy(Ref.legacySighash unsigned legacyScript)
       signed=unsigned{sigTxIn=V.imap(\i input->if i==1 then input{sigTxiScriptSig=BL.fromStrict(Ref.p2pkhScriptSig der legacyPoint)}else input)(sigTxIn unsigned)}
       environment root=if root==cmr then mkEnv signed 0 tap root else Nothing
       message=case environment cmr >>= (\e->J.fastEval(J.unwrap(J.jetSubst sigMsg))e())of Just m->w256ToBytes m;_->error "silent payment native message"
       aggregateSecret=(Ref.evenSecret outputSecret+legacy)`mod`R.n
       (c,(e,s))=Ref.prove374 aggregateSecret scan message
       Just(x,y)=legacyPoint
       proof=((w256(R.pubkeyOf outputSecret),(w8(if even y then 2 else 3),w256 x)),(derW der,(pointW c,(w256 e,w256 s))))
   in(environment,proof)
  (goodEnv,good)=make(dummyOutpoint 0)(dummyOutpoint 1)Nothing 99000
  (orderedEnv,ordered)=make(Outpoint(hashFromInteger 123)1)(Outpoint(hashFromInteger 123)256)Nothing 99000
  (divertEnv,divert)=make(dummyOutpoint 0)(dummyOutpoint 1)(Just(R.pubkeyOf 99))99000
  (underpayEnv,underpay)=make(dummyOutpoint 0)(dummyOutpoint 1)Nothing 98999
  (keys,(der,(c,(e,s))))=good
  (d512,(d32,d16))=der
  vectors=[Vector "complete eligible-input provenance and BIP374 proof" goodEnv good Accept,
   Vector "same txid indices1/256 use wire-byte ordering" orderedEnv ordered Accept,
   Vector "fresh valid proof cannot divert silent output" divertEnv divert Reject,
   Vector "fresh valid proof cannot alter conservation fee" underpayEnv underpay Reject,
   Vector "noncanonical BIP374 challenge e=n" goodEnv(keys,(der,(c,(w256 R.n,s))))Reject,
   Vector "noncanonical BIP374 response s=n" goodEnv(keys,(der,(c,(e,w256 R.n))))Reject,
   Vector "shared point changed at its single occurrence" goodEnv(keys,(der,(pointW R.gPt,(e,s))))Reject,
   Vector "raw DER witness disagrees with actual scriptSig" goodEnv(keys,((d512,(d32,w16(fromWord16 d16+1))),(c,(e,s))))Reject,
   Vector "wrong P2TR output-key extraction" goodEnv((w256(R.pubkeyOf 77),snd keys),(der,(c,(e,s))))Reject]
