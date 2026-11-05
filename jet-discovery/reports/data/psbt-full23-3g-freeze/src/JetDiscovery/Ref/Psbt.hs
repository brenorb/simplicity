-- | Independent bounded BIP174 finalizer/extractor model. Complete published
-- mixed legacy-P2SH / P2SH-P2WSH workflow; no general Script interpreter claim.
module JetDiscovery.Ref.Psbt where
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Data.Serialize(Get,runGet,runPut,getWord8,getWord16le,getWord32le,getWord64le,getBytes,isEmpty)
import Control.Monad(replicateM,unless)
import Data.List(nub)
import Simplicity.Bitcoin.DataTypes
import JetDiscovery.Tx
import JetDiscovery.Ref.BitcoinGrowth(sha256d,le32,le64)
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.SilentPayment as K
import qualified JetDiscovery.Ref.NumericDlc as E
import qualified JetDiscovery.Ref.PaymentCode as P
import JetDiscovery.Corpus.Ripemd(ripemd160Ref)

type Map=[(B.ByteString,B.ByteString)]
data Psbt=Psbt{globalMap::Map,inputMaps::[Map],outputMaps::[Map]}deriving(Eq,Show)
data Session=Session{sourcePsbt::Psbt,sourceRaw::B.ByteString,expectedPsbt::B.ByteString,expectedNetwork::B.ByteString
 ,unsignedTx::SigTx,redeemScripts::[B.ByteString],witnessScript::B.ByteString,publics::[R.Pt],signatures::[(Integer,Integer)],signatureBytes::[B.ByteString]}
integer :: B.ByteString -> Integer
integer=B.foldl'(\a x->a*256+toInteger x)0
hash160=ripemd160Ref.hashToBytes.sha256
getCompact :: Get Int
getCompact=do
 tag<-getWord8
 value<-case tag of
  253->do x<-getWord16le;unless(x>=253)(fail "nonminimal CompactSize16");return(toInteger x)
  254->do x<-getWord32le;unless(x>=65536)(fail "nonminimal CompactSize32");return(toInteger x)
  255->do x<-getWord64le;unless(x>=2^32)(fail "nonminimal CompactSize64");return(toInteger x)
  _->return(toInteger tag)
 unless(value<=1000000)(fail "local PSBT byte/count bound1000000")
 return(fromInteger value)
getString=getCompact>>=getBytes
getMap :: Get Map
getMap=go []
 where
  go values=do
   key<-getString
   if B.null key then return(reverse values)else do
    unless(not(key`elem`map fst values))(fail "duplicate PSBT key")
    _<-either fail return(runGet getCompact key)
    value<-getString
    go((key,value):values)
-- The complete96-record inventory has its separate structural v0/v2 reader.
-- This reference intentionally accepts only v0 sessions for its finalizer.
parsePsbt :: B.ByteString -> Either String Psbt
parsePsbt=runGet $do
 magic<-getBytes 5;unless(magic==unhex "70736274ff")(fail "PSBT magic")
 globals<-getMap
 unless(maybe True(==B.replicate 4 0)(lookup(unhex "fb")globals))(fail "reference finalizer only supports v0")
 raw<-maybe(fail "missing unsigned tx")return(lookup(unhex "00")globals)
 parsed<-either fail return(parseRawTx raw)
 unless(all(B.null.riScriptSig)(rtIns parsed)&&all null(rtWitness parsed)&&runPut(putNoWitnessTx(rawToSigTx parsed))==raw)(fail "PSBT unsigned tx must be exact non-witness bytes with empty scriptSigs")
 inputs<-replicateM(length(rtIns parsed))getMap;outputs<-replicateM(length(rtOuts parsed))getMap
 done<-isEmpty;unless done(fail "trailing PSBT bytes")
 return(Psbt globals inputs outputs)
compact :: Int -> B.ByteString
compact n
 |n<0=error "negative CompactSize"
 |n<253=B.singleton(fromIntegral n)
 |n<65536=unhex "fd"<>B.take 2(le32(toInteger n))
 |otherwise=unhex "fe"<>le32(toInteger n)
string bytes=compact(B.length bytes)<>bytes
serializeMap values=B.concat[string key<>string value|(key,value)<-values]<>B.singleton 0
serializePsbt p=unhex "70736274ff"<>B.concat(map serializeMap(globalMap p:inputMaps p++outputMaps p))
stack xs=compact(length xs)<>B.concat(map string xs)
field key values=maybe(error("missing PSBT field"++show key))id(lookup(B.singleton key)values)
pubkeys script
 |B.length script==71&&B.take 2 script==unhex "5221"&&B.index script 35==33&&B.drop 69 script==unhex "52ae"=
  map(K.decodeCompressed .(\offset->B.take 33(B.drop offset script)))[2,36]
 |otherwise=error "outside exact2of2 compressed multisig profile"
derAll :: (Integer,Integer) -> B.ByteString
derAll(r,s)=B.pack[0x30,fromIntegral(B.length body)]<>body<>B.singleton 1
 where
  body=B.concat(map number[r,s])
  number value=let raw=B.dropWhile(==0)(R.bytesFromInt value);bytes=if B.null raw then B.singleton 0 else if B.head raw>=128 then B.singleton 0<>raw else raw in B.pack[2,fromIntegral(B.length bytes)]<>bytes
txout output=le64(toInteger(txoValue output))<>string(BL.toStrict(txoScript output))
prevout input=case sigTxiPreviousOutpoint input of Outpoint hash index->hashToBytes hash<>le32(toInteger index)
bip143All index script tx=sha256d(le32(toInteger(sigTxVersion tx))
 <>sha256d(B.concat(map prevout inputs))<>sha256d(B.concat[le32(toInteger(sigTxiSequence i))|i<-inputs])
 <>prevout input<>string script<>le64(toInteger(sigTxiValue input))<>le32(toInteger(sigTxiSequence input))
 <>sha256d(B.concat(map txout(V.toList(sigTxOut tx))))<>le32(toInteger(sigTxLock tx))<>le32 1)
 where inputs=V.toList(sigTxIn tx);input=inputs!!index
messages session=[legacy,legacy,witness,witness]
 where
  legacy=P.legacyAll0(unsignedTx session)(redeemScripts session!!0)
  witness=bip143All 1(witnessScript session)(unsignedTx session)
finalScript0 session sigs=unhex "00"<>B.concat[ B.singleton(fromIntegral(B.length raw))<>raw|raw<-map derAll(take 2 sigs)++[redeemScripts session!!0]]
finalScript1 session=B.singleton 34<>redeemScripts session!!1
finalStack1 session sigs=[B.empty]++map derAll(drop 2 sigs)++[witnessScript session]
withSignatures session sigs=source{inputMaps=map(map replace)(inputMaps source)}
 where
  source=sourcePsbt session
  replacements=zip[unhex "02"<>K.compressed point|point<-publics session](map derAll sigs)
  replace (key,value)=(key,maybe value id(lookup key replacements))
finalize session sigs=source{inputMaps=[retain(inputMaps source!!0)++[(unhex "07",finalScript0 session sigs)]
 ,retain(inputMaps source!!1)++[(unhex "07",finalScript1 session),(unhex "08",stack(finalStack1 session sigs))]]}
 where
  source=sourcePsbt session
  -- Exact session has UTXO/partial-signature/sighash/redeem/witness/keypaths.
  -- Unknown/proprietary keys are retained, but unsupported schemas earn no claim.
  retain=filter(\(key,_)->B.head key`elem`[0,1]||B.head key>0x18)
finalTx session sigs=(unsignedTx session){sigTxIn=V.imap(\i input->input{sigTxiScriptSig=BL.fromStrict(if i==0 then finalScript0 session sigs else finalScript1 session)})(sigTxIn(unsignedTx session))}
network session sigs=B.take 4 raw<>unhex "0001"<>B.take(B.length raw-8)(B.drop 4 raw)<>B.singleton 0<>stack(finalStack1 session sigs)<>B.drop(B.length raw-4)raw
 where raw=runPut(putNoWitnessTx(finalTx session sigs))
verifySigs session sigs=length sigs==4&&and(zipWith3 E.ecdsaVerify(publics session)(messages session)sigs)
 &&all(\(r,s)->r>=2^248&&r<R.n&&s>=2^248&&s<=R.n`div`2)sigs
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
freshSignatures session=do
 rows<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth9/psbt-published-signer-private-fixtures.tsv"
 let secrets=[maybe(error "missing source signer private fixture")(integer.unhex)(lookup child[(i,k)|[i,k]<-rows])|child<-["0","1","2","3"]]
     -- Deterministic public nonces only for these published test-only secrets.
     -- Move the high-r padding from legacy slot1 to witness slot2 to exercise
     -- both independent PSBT/script/witness length computations.
     sign i d msg=head[(r,s)|nonce<-[11..],let r=R.xOnly(R.pointMul R.gPt nonce)`mod`R.n,
                      let raw=((integer msg+r*d)*E.inverse nonce)`mod`R.n,
                      let s=min raw(R.n-raw),r>=2^248,s>=2^248,(r>=2^255)==(i==2)]
     result=zipWith3 sign [0::Int ..]secrets(messages session)
 unless(map(R.pointMul R.gPt)secrets==publics session&&verifySigs session result&&result/=signatures session)(fail "published signer keys/fresh valid signature fixtures")
 return result
fixture=do
 rows<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth9/psbt-all-inline-vectors.tsv"
 let raw n=case[row!!8|row<-rows,row!!0=="0174",row!!1==show n]of[v]->unhex v;_->error "PSBT source ordinal"
     source=raw 40;expected=raw 41;wire=raw 42
 parsed<-either fail return(parsePsbt source)
 unsigned<-either fail return(parseRawTx(field 0(globalMap parsed)))
 let [map0,map1]=inputMaps parsed
     [redeem0,redeem1]=map(field 4)[map0,map1];ws=field 5 map1
 previous<-either fail return(parseRawTx(field 0 map0))
 let tx0=rawToSigTx unsigned
     [i0,i1]=V.toList(sigTxIn tx0)
     Outpoint h0 index0=sigTxiPreviousOutpoint i0
     previousOut=rtOuts previous!!fromIntegral index0
     witOut=field 1 map1
     utxo0=TxOutput(roValue previousOut)(BL.fromStrict(roScript previousOut))
     amount1=fromInteger(integer(B.reverse(B.take 8 witOut)))
     script1=B.drop 9 witOut
     tx=tx0{sigTxIn=V.fromList[i0{sigTxiTxo=utxo0},i1{sigTxiTxo=TxOutput amount1(BL.fromStrict script1)}]}
     keys=pubkeys redeem0++pubkeys ws
     raws=[maybe(error "missing source partial signature")id(lookup(unhex "02"<>K.compressed key)values)|(values,keys')<-[(map0,take 2 keys),(map1,drop 2 keys)],key<-keys']
     sigs=map(maybe(error "noncanonical source DER/ALL")id.P.parseDerAll)raws
     session=Session parsed source expected wire tx[redeem0,redeem1]ws keys sigs raws
 unless(hashToBytes h0==sha256d(field 0 map0)&&B.length witOut==32&&B.index witOut 8==23&&redeem1==unhex "0020"<>hashToBytes(sha256 ws)
  &&roScript previousOut==unhex "a914"<>hash160 redeem0<>unhex "87"&&script1==unhex "a914"<>hash160 redeem1<>unhex "87"
  &&length(nub keys)==4&&all(==unhex "01000000")[field 3 map0,field 3 map1]
  &&serializePsbt parsed==source&&verifySigs session sigs&&map derAll sigs==raws
  &&serializePsbt(finalize session sigs)==expected&&network session sigs==wire)(fail "complete source PSBT finalizer/extractor relation mismatch")
 return session
