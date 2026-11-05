module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Simplicity.Bitcoin.DataTypes
import JetDiscovery.Tx
import qualified JetDiscovery.Ref.ReserveProof as Ref
import qualified JetDiscovery.Ref.Bip340 as EC
import System.Exit(exitFailure)
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
main=do
 raw<-unhex.filter(/='\n') <$>readFile "vendor-specs/bitcoin-growth2/bip341-group-0-unsigned.hex"
 utxos<-map(fields.filter(/='\r')).drop 1.lines <$>readFile "vendor-specs/bitcoin-growth2/bip341-group-0-utxos.tsv"
 rows<-map(fields.filter(/='\r')).drop 1.lines <$>readFile "vendor-specs/bitcoin-growth2/bip341-all01-vectors.tsv"
 parsed<-either fail return(parseRawTx raw)
 let tx0=rawToSigTx parsed
     tx=tx0{sigTxIn=V.imap(\i input->case utxos!!i of
        [j,amount,script]|read j==i->input{sigTxiTxo=TxOutput(read amount)(BL.fromStrict(unhex script))}
        _->error "bad utxo row")(sigTxIn tx0)}
 assert "all published compatible ALL01 cases present"(length rows==1&&length utxos==V.length(sigTxIn tx))
 mapM_(\[_,_,idx,digest,sig]->do
   let index=read idx;actual=Ref.sighashAll tx index
       pk=B.drop 2(BL.toStrict(sigTxiScript(sigTxIn tx V.!fromIntegral index)))
   assert("BIP341 upstream digest input"++idx)(actual==unhex digest)
   assert("BIP341 upstream signature input"++idx)(EC.verify pk actual(unhex sig)))rows
 let msg=C.pack "Some Message";commit=Ref.commitment msg
     p2tr d=unhex "5120"<>EC.bytesFromInt(EC.pubkeyOf d)
     proofTx=mkTx 2[mkInput(Outpoint(hashFromBytes(B.reverse commit))0)0(BL.fromStrict(unhex "51"))0xffffffff,
       mkInput(dummyOutpoint 1)50000(BL.fromStrict(p2tr 11))0xffffffff,
       mkInput(dummyOutpoint 2)60000(BL.fromStrict(p2tr 22))0xffffffff][mkOutput 110000(unhex "6a")]0
     sigs=Ref.signatures proofTx 11 22
     wire=Ref.wireProof proofTx sigs
 proof<-either fail return(parseRawTx wire)
 assert "normative BIP127 single-SHA commitment"(hex commit=="30896246cd560f641d84e2ddcd9ee0f8fd74e4547be75aa7d6464f75dd372dff")
 assert "both independently indexed ownership signatures"(Ref.verifySignatures proofTx(EC.pubkeyOf 11)(EC.pubkeyOf 22)sigs)
 assert "canonical actual proof transport"(rtVersion proof==2&&rtLock proof==0&&length(rtIns proof)==3
   &&map riScriptSig(rtIns proof)==replicate 3 B.empty&&map riSequence(rtIns proof)==replicate 3 0xffffffff
   &&(case riOutpoint(head(rtIns proof))of Outpoint h i->hashToBytes h==B.reverse commit&&i==0)
   &&map roValue(rtOuts proof)==[110000]&&map roScript(rtOuts proof)==[unhex "6a"]
   &&rtWitness proof==[[],[head sigs<>B.singleton 1],[sigs!!1<>B.singleton 1]])
 writeFile "vendor-specs/bitcoin-growth2/bip127-derived-proof.hex"(hex wire++"\n")
 writeFile "vendor-specs/bitcoin-growth2/bip127-derived-proof.tsv"("kind\tvalue\nmessage_utf8\tSome Message\ncommitment_raw\t"++hex commit++"\nreserve_sum_sat\t110000\ninput1_all01_digest\t"++hex(Ref.sighashAll proofTx 1)++"\ninput2_all01_digest\t"++hex(Ref.sighashAll proofTx 2)++"\ntransport_bytes\t"++show(B.length wire)++"\n")
