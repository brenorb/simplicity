{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | The complete published BIP174 mixed legacy/nested-SegWit session as a
-- client finalizer/extractor relation. Public transaction/maps are compiled
-- session parameters. Actual signature data appears once in the witness.
module JetDiscovery.Lib.Psbt(entry,Proof,clientKernel)where
import Prelude hiding(drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Vector as V
import Data.Serialize(runPut)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term(Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.DataTypes
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Corpus.ContractExpansion(ecdsaVerify)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer(ctxWith)
import qualified JetDiscovery.Lib.TaprootTx1 as T
import qualified JetDiscovery.Ref.Psbt as Ref
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.SilentPayment as K
import JetDiscovery.Ref.BitcoinGrowth(sha256d,le32,le64)
import JetDiscovery.Types
import JetDiscovery.Tx

type Sig=(Word256,Word256)
type GE=(Word256,Word256)
type Sigs=((Sig,Sig),(Sig,Sig))
type Hashes=(Word256,(Word256,(Word256,Word256)))
type Proof=(Sigs,Hashes)
type Context=(Sigs,Ctx8)
data Part=Bytes B.ByteString|Signature Int|LegacyLength|WitnessLength
sigAt :: Core t => Int -> t Sigs Sig
sigAt 0=ooh
sigAt 1=oih
sigAt 2=ioh
sigAt 3=iih
sigAt _=error "PSBT signature slot"
same :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a()
same a b=(a&&&b)>>>eq>>>verify
allChecks :: (Assert t,TyC a) => [t a()] -> t a()
allChecks=L.foldl'(\a b->(a&&&b)>>>unit)unit
hashBytes :: Assert t => B.ByteString -> t()Word256
hashBytes bytes=ctx8Init>>>T.appendConst bytes>>>ctx8Finalize
double :: Assert t => t Word256 Word256
double=((unit>>>ctx8Init)&&&iden)>>>ctx8Add32>>>ctx8Finalize
highR :: Assert t => t Sig Bit
highR=(konst(w256(2^255))&&&oh)>>>A.le word256
sigLen :: Assert t => t Sig Word8
sigLen=(highR&&&unit)>>>cond(konst(w8 72))(konst(w8 71))
add8 :: (Assert t,TyC a) => t a Word8 -> t a Word8 -> t a Word8
add8 a b=(a&&&b)>>>A.add word8>>>ih
-- Both 32-byte r and 33-byte zero-padded r, 32-byte positive low-S, then ALL01.
-- The same computed length prefix is used for PSBT values and script pushes.
signaturePart :: Assert t => t Sigs Sig -> t Context Context
signaturePart select=T.append(select>>>sigLen)ctx8Add1
 >>>(((oh>>>select>>>highR)&&&iden)>>>cond(T.constant(unhex "3045022100"))(T.constant(unhex "30440220")))
 >>>T.append(select>>>oh)ctx8Add32>>>T.constant(unhex "0220")>>>T.append(select>>>ih)ctx8Add32>>>T.constant(unhex "01")
hashParts :: forall t. Assert t => [Part] -> t Sigs Word256
hashParts parts=(iden&&&(unit>>>ctx8Init))>>>L.foldl'(>>>)iden(map append parts)>>>ih>>>ctx8Finalize
 where
  append :: Part -> t Context Context
  append(Bytes bytes)=T.constant bytes
  append(Signature slot)=signaturePart(sigAt slot)
  append LegacyLength=T.append(add8(konst(w8 75))(add8(sigAt 0>>>sigLen)(sigAt 1>>>sigLen)))ctx8Add1
  append WitnessLength=T.append(add8(konst(w8 76))(add8(sigAt 2>>>sigLen)(sigAt 3>>>sigLen)))ctx8Add1
legacyScript :: Ref.Session -> [Part]
legacyScript session=[Bytes(unhex "00"),Signature 0,Signature 1,Bytes(Ref.string(Ref.redeemScripts session P.!!0))]
witnessStack :: Ref.Session -> [Part]
witnessStack session=[Bytes(unhex "0400"),Signature 2,Signature 3,Bytes(Ref.string(Ref.witnessScript session))]
psbtHead session=unhex "70736274ff"<>Ref.serializeMap(Ref.globalMap(Ref.sourcePsbt session))
psbtTail=B.concat.map Ref.serializeMap.Ref.outputMaps.Ref.sourcePsbt
psbtIn :: Ref.Session -> [Part]
psbtIn session=[Bytes(psbtHead session)]++concatMap input(Ref.inputMaps(Ref.sourcePsbt session))++[Bytes(psbtTail session)]
 where
  keys=map((unhex "02"<>).K.compressed)(Ref.publics session)
  input fields=concatMap record fields++[Bytes(unhex "00")]
  record(key,value)=case L.elemIndex key keys of
   Just slot->[Bytes(Ref.string key),Signature slot]
   Nothing->[Bytes(Ref.string key<>Ref.string value)]
psbtFinal :: Ref.Session -> [Part]
psbtFinal session=[Bytes(psbtHead session<>retained0<>unhex "0107"),LegacyLength]++legacyScript session
 ++[Bytes(unhex "00"<>retained1<>unhex "0107"<>Ref.string(Ref.finalScript1 session)<>unhex "0108"),WitnessLength]
 ++witnessStack session++[Bytes(unhex "00"<>psbtTail session)]
 where
  [fields0,fields1]=Ref.inputMaps(Ref.sourcePsbt session)
  retained=B.concat.map(\(key,value)->Ref.string key<>Ref.string value).filter(\(key,_)->B.head key`elem`[0,1]||B.head key>0x18)
  retained0=retained fields0;retained1=retained fields1
network :: Bool -> Ref.Session -> [Part]
network includeWitness session=[Bytes(version<>marker<>unhex "02"<>Ref.prevout i0),LegacyLength]++legacyScript session
 ++[Bytes(seqBytes i0<>Ref.prevout i1<>Ref.string(Ref.finalScript1 session)<>seqBytes i1<>unhex "02"<>outputs<>emptyLegacyWitness)]
 ++(if includeWitness then witnessStack session else[])++[Bytes(le32(toInteger(sigTxLock tx)))]
 where
  tx=Ref.unsignedTx session;[i0,i1]=V.toList(sigTxIn tx)
  version=le32(toInteger(sigTxVersion tx));seqBytes=le32.toInteger.sigTxiSequence
  outputs=B.concat(map Ref.txout(V.toList(sigTxOut tx)))
  marker=if includeWitness then unhex "0001"else B.empty
  emptyLegacyWitness=if includeWitness then unhex "00"else B.empty
legacyDigest :: Assert t => Ref.Session -> t()Word256
legacyDigest session=hashBytes(runPut(putNoWitnessTx tx{sigTxIn=V.imap script(sigTxIn tx)})<>le32 1)>>>double
 where
  tx=Ref.unsignedTx session
  script i input=input{sigTxiScriptSig=if i==0 then BL.fromStrict(Ref.redeemScripts session P.!!0)else BL.empty}
witnessDigest :: Assert t => Ref.Session -> t()Word256
witnessDigest session=ctx8Init>>>T.appendConst(le32(toInteger(sigTxVersion tx)))
 >>>ctxWith(hashBytes(B.concat(map Ref.prevout inputs))>>>double)ctx8Add32
 >>>ctxWith(hashBytes(B.concat(map seqBytes inputs))>>>double)ctx8Add32
 >>>T.appendConst(Ref.prevout i1<>Ref.string(Ref.witnessScript session)<>le64(toInteger(sigTxiValue i1))<>seqBytes i1)
 >>>ctxWith(hashBytes(B.concat(map Ref.txout(V.toList(sigTxOut tx))))>>>double)ctx8Add32
 >>>T.appendConst(le32(toInteger(sigTxLock tx))<>le32 1)>>>ctx8Finalize>>>double
 where
  tx=Ref.unsignedTx session;inputs=V.toList(sigTxIn tx);i1=inputs P.!!1
  seqBytes=le32.toInteger.sigTxiSequence
pointW(Just(x,y))=(w256 x,w256 y)
pointW Nothing=error "PSBT source infinity"
verifySignatures :: forall t. Assert t => Ref.Session -> t Sigs()
verifySignatures session=(iden&&&(unit>>>(legacyDigest session&&&witnessDigest session)))>>>allChecks[slot i|i<-[0..3]]
 where
  ecdsa :: t((GE,Word256),Sig)()
  ecdsa=ecdsaVerify
  profile :: t Sig()
  profile=allChecks[(konst(w256(2^248))&&&oh)>>>A.le word256>>>verify,
                    (konst(w256(2^248))&&&ih)>>>A.le word256>>>verify,
                    (ih&&&konst(w256(R.n`div`2)))>>>A.le word256>>>verify]
  slot i=allChecks[oh>>>sigAt i>>>profile,((konst(pointW(Ref.publics session P.!!i))&&&(ih>>>(if i<2 then oh else ih)))&&&(oh>>>sigAt i))>>>ecdsa]
at i prim=konst(w32 i)>>>primitive prim>>>verify
hashW=w256FromBytes.hashToBytes.sha256
environment :: (Simplicity t,Primitive t) => Ref.Session -> t Sigs()
environment session=allChecks([same(unit>>>Tx.numInputs)(konst(w32 2)),same(unit>>>Tx.numOutputs)(konst(w32 2)),
 same(unit>>>primitive Prim.CurrentIndex)(konst(w32 0)),
 same(unit>>>primitive Prim.Version)(konst(w32(toInteger(sigTxVersion tx)))),
 same(unit>>>primitive Prim.LockTime)(konst(w32(toInteger(sigTxLock tx)))),
 same(at 0 Prim.InputScriptSigHash)(hashParts(legacyScript session)),
 same(at 1 Prim.InputScriptSigHash)(konst(hashW(Ref.finalScript1 session)))]
 ++concat[bindInput i input|(i,input)<-zip[0..](V.toList(sigTxIn tx))]
 ++concat[bindOutput i output|(i,output)<-zip[0..](V.toList(sigTxOut tx))])
 where
  tx=Ref.unsignedTx session
  bindInput i input=case sigTxiPreviousOutpoint input of
   Outpoint h j->[same(at i Prim.InputPrevOutpoint)(konst(w256FromBytes(hashToBytes h),w32(toInteger j))),
                  same(at i Prim.InputValue)(konst(w64(toInteger(sigTxiValue input)))),
                  same(at i Prim.InputScriptHash)(konst(hashW(BL.toStrict(sigTxiScript input)))),
                  same(at i Prim.InputSequence)(konst(w32(toInteger(sigTxiSequence input))))]
  bindOutput i output=[same(at i Prim.OutputValue)(konst(w64(toInteger(txoValue output)))),
                       same(at i Prim.OutputScriptHash)(konst(hashW(BL.toStrict(txoScript output))))]
clientKernel :: forall t. (Simplicity t,Primitive t) => Ref.Session -> t Proof()
clientKernel session=allChecks[oh>>>verifySignatures session,oh>>>environment session,
 same(oh>>>hashParts(psbtIn session))ioh,
 same(oh>>>hashParts(psbtFinal session))iioh,
 same(oh>>>hashParts(network False session)>>>double)(ih>>>ih>>>ih>>>oh),
 same(oh>>>hashParts(network True session)>>>double)(ih>>>ih>>>ih>>>ih)]
proof :: Ref.Session -> [(Integer,Integer)] -> Proof
proof session sigs=(case map(\(r,s)->(w256 r,w256 s))sigs of [a,b,c,d]->((a,b),(c,d));_->error "four PSBT signatures",
 (hashW(Ref.serializePsbt(Ref.withSignatures session sigs)),(hashW(Ref.serializePsbt(Ref.finalize session sigs)),
  (w256FromBytes(sha256d(runPut(putNoWitnessTx(Ref.finalTx session sigs)))),w256FromBytes(sha256d(Ref.network session sigs))))))
changeClaim slot (sigs,(pre,(post,(txid,wtxid))))=(sigs,case slot of
 0->(inc pre,(post,(txid,wtxid)));1->(pre,(inc post,(txid,wtxid)));2->(pre,(post,(inc txid,wtxid)));_->(pre,(post,(txid,inc wtxid))))
 where inc x=w256(fromWord256 x+1)
entry :: IO Entry
entry=do
 session<-Ref.fixture;fresh<-Ref.freshSignatures session
 let original=Ref.signatures session;tx=Ref.finalTx session original;w=proof session original
     mk name actual index value expected=Vector name(mkEnv actual index defaultTap)value expected
     usual name actual value expected=mk name actual 0 value expected
     signaturesCase name sigs expected=usual name(Ref.finalTx session sigs)(proof session sigs)expected
     corrupt i=[if i==j then(r+1,s)else(r,s)|(j,(r,s))<-zip[0..]original]
     highS=case original of (r,s):rest->(r,R.n-s):rest;_->error "four PSBT signatures"
     changeInput i f=tx{sigTxIn=V.imap(\j input->if i==j then f input else input)(sigTxIn tx)}
     changeOutput i f=tx{sigTxOut=V.imap(\j output->if i==j then f output else output)(sigTxOut tx)}
     alteredScript i=changeInput i(\x->x{sigTxiScriptSig=BL.cons 0(sigTxiScriptSig x)})
     flippedOutpoint x=case sigTxiPreviousOutpoint x of Outpoint h i->x{sigTxiPreviousOutpoint=Outpoint(hashFromInteger(R.intFromBytes(B.reverse(hashToBytes h))))i}
     rejects name actual=usual name actual w Reject
 return(Entry "app-bip174-mixed-psbt-finalizer-extractor"
  "BIP174 mixed legacy/nested-SegWit four-signature finalizer and network extractor"
  "BIP174 pinned a0c977f3755da6476b955677ca9318334a2432c4, complete published workflow records40/41/42; standard legacy ALL and BIP143 ALL"
  BitcoinApp(Derived "Full published partial/final PSBT and network bytes, four real DER signatures, second fresh complete signed session, independently computed hashes and same-CMR transaction/proof negatives")
  ["CLIENT MODE: exact bounded per-session finalizer/extractor for the published v0 workflow; no general PSBT parser or onchain P2SH/P2WSH spend claim",
   "Two inputs/two outputs: legacy P2SH2-of2 and nested P2SH-P2WSH2-of2; fixed authenticated unsigned transaction, input UTXOs, script keys and full retained metadata as session constants",
   "Verifies all four actual ECDSA signatures on native-computed legacy ALL and BIP143 ALL messages, with checked 32-byte positive scalars, optional canonical r pad, low-S and ALL01 only",
   "One structured witness contains four logical signatures once and four separately checked digest claims; native streaming serialization covers complete partial/final maps, final scriptSig/witness fields and network bytes",
   "Single SHA256 PSBT input/final record commitments; distinct SHA256d txid from no-witness bytes and SHA256d wtxid from marker/flag and complete witness serialization",
   "Actual finalized transaction primitive view checks current input0, both prevout hashes/indices/values/scripts/sequences and final scriptSig hashes, version/locktime, both output values/scripts and exact counts",
   "Syntactic map/transport decoding, digest claims of supplied PSBT/network bytes and session selection are client boundaries. The primitive view does not expose the final witness stack; wtxid binds the exact separately supplied network wire digest. Actual UTXO existence/confirmation and broadcast remain external. BIP370 and other PSBT/Script profiles are inventoried but not implemented here"]
  (boundProgram(clientKernel session))
  ([signaturesCase "published full signed PSBT to exact finalized PSBT and network transaction" original Accept,
    signaturesCase "four fresh valid signatures and complete regenerated PSBT/network session" fresh Accept]
   ++[signaturesCase("changed mathematical signature slot "++show i++" with matching regenerated byte/hash claims")(corrupt i)Reject|i<-[0..3]]
   ++[signaturesCase "high-S mathematical alias rejected by canonical profile" highS Reject]
   ++[usual("changed digest claim: "++name)tx(changeClaim i w)Reject|(i,name)<-zip[0..]["partial PSBT SHA256","final PSBT SHA256","txid","wtxid"]]
   ++[rejects "changed actual legacy finalized scriptSig"(alteredScript 0),rejects "changed actual nested SegWit scriptSig"(alteredScript 1),
      rejects "display-order hash in actual prevout instead of raw bytes"(changeInput 1 flippedOutpoint),
      rejects "changed actual witness UTXO value"(changeInput 1(\x->x{sigTxiTxo=TxOutput(sigTxiValue x+1)(sigTxiScript x)})),
      rejects "changed actual legacy UTXO script"(changeInput 0(\x->x{sigTxiTxo=TxOutput(sigTxiValue x)(BL.fromStrict(unhex "51"))})),
      rejects "changed actual output destination"(changeOutput 0(\x->mkOutput(txoValue x)(unhex "51"))),
      rejects "changed actual output amount"(changeOutput 1(\x->x{txoValue=txoValue x+1})),
      rejects "changed actual sequence"(changeInput 1(\x->x{sigTxiSequence=sigTxiSequence x-1})),
      rejects "changed actual locktime"(tx{sigTxLock=1}),rejects "changed actual transaction version"(tx{sigTxVersion=1}),
      mk "different actual current input" tx 1 w Reject,
      rejects "additional actual output"(tx{sigTxOut=V.snoc(sigTxOut tx)(mkOutput 0(unhex "6a"))})]))
