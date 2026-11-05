module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Vector as V
import Simplicity.Bitcoin.DataTypes
import JetDiscovery.Tx
import qualified JetDiscovery.Ref.NumericDlc as D
import qualified JetDiscovery.Ref.Bip340 as R
import System.Exit(exitFailure)
import Data.Serialize(runPut)
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
sig raw=(R.intFromBytes(B.take 32 raw),R.intFromBytes(B.drop 32 raw))
main=do
 rows<-map(fields.filter(/='\r')).drop 1.lines <$>readFile "vendor-specs/bitcoin-growth2/dlc-adaptor-all-vectors.tsv"
 assert "all11 official adaptor cases present"(length rows==11)
 mapM_(\[idx,kind,a,msg,x,y,key,signature,err,_]->do
  let parsed=D.parseAdaptor(unhex a)
  case(kind,parsed)of
   ("serialization",_)->assert("upstream serialization"++idx)((case parsed of Just p->D.serializeAdaptor p==unhex a;_->False)==(err=="-"))
   ("verification",Just p)->do
    let valid=D.verifyAdaptor(D.decodeCompressed(unhex x))(D.decodeCompressed(unhex y))(unhex msg)p
    assert("upstream adaptor verification"++idx)(valid==(err=="-"))
    if err/="-" then return()else do
     let k=R.intFromBytes(unhex key);plain=D.decrypt p k
     assert("upstream exact decryption"++idx)(plain==sig(unhex signature))
     assert("upstream exact recovery"++idx)(D.recover(D.decodeCompressed(unhex y))p plain==Just k)
     assert("upstream actual plaintext ECDSA"++idx)(D.ecdsaVerify(D.decodeCompressed(unhex x))(unhex msg)plain)
   ("recovery",Just p)->assert("upstream recovery"++idx)(D.recover(D.decodeCompressed(unhex y))p(sig(unhex signature))==if key=="-"then Nothing else Just(R.intFromBytes(unhex key)))
   _->assert("unexpected parse failure"++idx)False)rows
 [cross]<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth2/bip143-all01-crosscheck.tsv"
 case cross of
  [raw,amount,ws,expected]->do
   p<-either fail return(parseRawTx(unhex raw))
   assert "published BIP143 unsigned transaction has canonical base wire roundtrip"(runPut(putNoWitnessTx(rawToSigTx p))==unhex raw)
   let t=rawToSigTx p;t'=t{sigTxIn=V.map(\i->i{sigTxiTxo=TxOutput(read amount)BL.empty})(sigTxIn t)}
   assert "BIP143 published six-of-six ALL01 digest"(D.cetSighash(unhex ws)t'==unhex expected)
  _->fail "BIP143 fixture columns"
 let secrets=L.sortOn(D.compressed.R.pointMul R.gPt)[11,22]
     ws=B.singleton 0x52<>B.concat[B.singleton 33<>D.compressed(R.pointMul R.gPt d)|d<-secrets]<>unhex "52ae"
     funding=unhex "0020"<>hashToBytes(sha256 ws)
     tx=mkTx 2[mkInput(Outpoint(hashFromInteger 0xd1c000127)0)102000(BL.fromStrict funding)0xfffffffe]
        [mkOutput 43000(unhex "0014"<>B.replicate 20 0x11),mkOutput 58000(unhex "0014"<>B.replicate 20 0x22)]900000
     msg=D.cetSighash ws tx
     (r0,s0)=D.oracleAttest 37 101 4;(r1,s1)=D.oracleAttest 37 103 2
     public=R.liftX(R.pubkeyOf 37)
     y=(s0+s1)`mod`R.n;enc=R.pointMul R.gPt y
     adaptors=[D.encrypt sk enc msg(211+toInteger i*2)(212+toInteger i*2)|(i,sk)<-zip[0..]secrets]
     plain=map(\a->D.decrypt a y)adaptors
     wire=D.wireCet ws tx plain
 assert "numeric oracle signature-point sum"(R.pointAdd(D.oraclePoint public r0 4)(D.oraclePoint public r1 2)==enc)
 assert "both full adaptor and derived plaintext signatures"(and[D.verifyAdaptor(R.pointMul R.gPt sk)enc msg a&&D.ecdsaVerify(R.pointMul R.gPt sk)msg s|(sk,a,s)<-zip3 secrets adaptors plain])
 parsed<-either fail return(parseRawTx wire)
 assert "canonical complete standard DLC CET wire"(rtVersion parsed==2&&rtLock parsed==900000&&length(rtIns parsed)==1
   &&map riScriptSig(rtIns parsed)==[B.empty]&&map riSequence(rtIns parsed)==[0xfffffffe]
   &&and(zipWith(\rawInput input->case(riOutpoint rawInput,sigTxiPreviousOutpoint input)of
      (Outpoint h i,Outpoint actual j)->hashToBytes h==hashToBytes actual&&i==j)(rtIns parsed)(V.toList(sigTxIn tx)))
   &&map roValue(rtOuts parsed)==[43000,58000]&&map roScript(rtOuts parsed)==[unhex "0014"<>B.replicate 20 0x11,unhex "0014"<>B.replicate 20 0x22]
   &&rtWitness parsed==[[B.empty,D.derSignature(plain!!0),D.derSignature(plain!!1),ws]])
 writeFile "vendor-specs/bitcoin-growth3/numeric-dlc-derived-canonical-cet.hex"(hex wire++"\n")
 writeFile "vendor-specs/bitcoin-growth3/numeric-dlc-derived-canonical-cet.tsv"("kind\tvalue\nbip143_all01_digest\t"++hex msg++"\nnumeric_outcome\t42\nfunding_value_sat\t102000\npayout_a_sat\t43000\npayout_b_sat\t58000\nfee_sat\t1000\nfunding_witness_script\t"++hex ws++"\nencryption_key\t"++hex(D.compressed enc)++"\n")
