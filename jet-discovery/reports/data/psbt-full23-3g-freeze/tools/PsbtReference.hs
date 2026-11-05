module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Data.Serialize(runPut)
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.FFI.Jets as C
import qualified Simplicity.Bitcoin.Primitive as Prim
import Simplicity.Ty.Word(fromWord32,fromWord64)
import JetDiscovery.Ref.Psbt
import JetDiscovery.Ref.BitcoinGrowth(sha256d)
import JetDiscovery.Lib.Bytes(w32,w256ToBytes)
import JetDiscovery.Tx
import System.Exit(exitFailure)
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
main=do
 session<-fixture
 let sigs=signatures session;final=finalize session sigs;wire=network session sigs;tx=finalTx session sigs
 assert "full four source DER/ALL signatures verify real legacy/BIP143 messages"(verifySigs session sigs)
 mapM_(\(i,message)->putStrLn("source message"++show i++"="++hex message))(zip[0::Int ..](messages session))
 assert "complete source final PSBT byte equality"(serializePsbt final==expectedPsbt session)
 assert "complete source extracted network byte equality"(wire==expectedNetwork session)
 parsed<-either fail return(parseRawTx wire)
 assert "network parser/base no-witness writer byte equality"(runPut(putNoWitnessTx(rawToSigTx parsed))==runPut(putNoWitnessTx tx))
 assert "full finalized network has empty legacy witness plus exact four-item SegWit witness"(rtWitness parsed==[[],finalStack1 session sigs])
 let rawTxid=sha256d(runPut(putNoWitnessTx tx));rawWtxid=sha256d wire
 putStrLn("raw txid="++hex rawTxid++" raw wtxid="++hex rawWtxid)
 assert "txid and wtxid are distinct actual digests"(rawTxid/=rawWtxid)
 let original=head sigs;broken=(fst original+1,snd original):tail sigs
 assert "changed partial signature rejects mathematical verification"(not(verifySigs session broken))
 assert "changed partial signature changes final PSBT and extracted network bytes"(serializePsbt(finalize session broken)/=expectedPsbt session&&network session broken/=expectedNetwork session)
 assert "all finalized source maps retain UTXO and remove old signatures/keypaths/scripts"(map(map(B.head.fst))(inputMaps final)==[[0,7],[1,7,8]])
 fresh<-freshSignatures session
 assert "fresh complete four-signature session verifies and changes both resulting IDs"(verifySigs session fresh&&sha256d(network session fresh)/=rawWtxid&&sha256d(runPut(putNoWitnessTx(finalTx session fresh)))/=rawTxid)
 assert "fresh valid DER padding moves from legacy slot to SegWit witness slot"(map B.length(map derAll sigs)==[71,72,71,71]&&map B.length(map derAll fresh)==[71,71,72,71])
 mapM_(\(label,chosen)->checkWire session label chosen)[("source",sigs),("fresh",fresh)]
 writeFile "vendor-specs/bitcoin-growth9/psbt-finalizer-derived-wires.tsv"("case\tpartial_psbt\tfinal_psbt\tnetwork\tpartial_sha256\tfinal_sha256\ttxid_raw\twtxid_raw\n"++concat[wireRow session label selected|(label,selected)<-[("source",sigs),("fresh",fresh)]])
wireRow session label sigs=let partial=serializePsbt(withSignatures session sigs);final=serializePsbt(finalize session sigs);wire=network session sigs
 in foldr1(\a b->a++"\t"++b)(label:map hex[partial,final,wire,hashToBytes(sha256 partial),hashToBytes(sha256 final),sha256d(runPut(putNoWitnessTx(finalTx session sigs))),sha256d wire])++"\n"
checkWire session label sigs=do
 let tx=finalTx session sigs;wire=network session sigs;Just env=mkEnv tx 0 defaultTap(hashFromInteger 1)
 parsed<-either fail return(parseRawTx wire)
 assert(label++" complete standard transaction/witness serialization")(runPut(putNoWitnessTx(rawToSigTx parsed))==runPut(putNoWitnessTx tx)&&rtWitness parsed==[[],finalStack1 session sigs])
 let hashOf=hashToBytes.sha256.BL.toStrict
     input i index=let raw=rtIns parsed!!i;inp=sigTxIn tx V.!i;Outpoint hash n=riOutpoint raw
                       expectedScript=hashOf(sigTxiScriptSig inp);expectedSpent=hashOf(sigTxiScript inp)
                       isWord v=case v of Just(Right a)->Just(w256ToBytes a);_->Nothing
                       amount v=case v of Just(Right a)->Just(fromWord64 a);_->Nothing
                       prev=(C.input_prev_outpoint env index,Prim.primSem Prim.InputPrevOutpoint index env)
                   in case prev of
                    (Just(Right(h,j)),Just(Right(hs,js)))->w256ToBytes h==hashToBytes hash&&w256ToBytes hs==hashToBytes hash&&fromWord32 j==toInteger n&&fromWord32 js==toInteger n
                      &&isWord(C.input_script_sig_hash env index)==Just expectedScript&&isWord(Prim.primSem Prim.InputScriptSigHash index env)==Just expectedScript
                      &&isWord(C.input_script_hash env index)==Just expectedSpent&&amount(C.input_value env index)==Just(toInteger(sigTxiValue inp))
                    _->False
     output i index=let out=rtOuts parsed!!i in case(C.output_script_hash env index,C.output_value env index)of
      (Just(Right h),Just(Right amount))->w256ToBytes h==hashToBytes(sha256(roScript out))&&fromWord64 amount==toInteger(roValue out)
      _->False
 mapM_(\i->assert(label++" actual C/Haskell raw outpoint/scriptSig/UTXO boundary "++show i)(input i(w32(toInteger i))))[0,1]
 mapM_(\i->assert(label++" actual C output value/script boundary "++show i)(output i(w32(toInteger i))))[0,1]
