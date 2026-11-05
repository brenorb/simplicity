-- Reconstruct the actual positive fixture from its logged, measured CMR.
module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import qualified Data.Vector as V
import Data.Serialize(runPut)
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SH
import qualified Simplicity.Bitcoin.Jets as J
import JetDiscovery.Tx
import JetDiscovery.Lib.Bytes(w256ToBytes)
import JetDiscovery.Lib.BitcoinFunding(fundingScript)
import qualified JetDiscovery.Ref.HdWallet as H
import qualified JetDiscovery.Ref.Bip340 as R
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
assert label ok=do putStrLn(label++"="++show ok);unless ok(error label)
main=do
 rows<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth6/bip32-wallet-derived.tsv"
 let first=head rows;secret=R.intFromBytes(unhex(first!!6));child=R.pointMul R.gPt secret
     cmr=hashFromBytes(unhex "13b7b854c3618be0efecc3b01d8d85366b73f828504dc45cf94c1578a63d97f0")
     Just output=H.keypathOutput child;tx=H.walletTx cmr(fst output)100000 99000 0
     Just env=mkEnv tx 0 defaultTap cmr
     Just message=J.fastEval(J.unwrap(J.jetSubst SH.sigAllHash))env()
     signature=R.sign secret(w256ToBytes message)(B.replicate 32 0)
     Just(_,y)=child;normalized=if even y then secret else R.n-secret
     tweak=R.intFromBytes(R.taggedHash "TapTweak"(R.bytesFromInt(R.xOnly child)))
     outputSecret=(normalized+tweak)`mod`R.n
     raw=runPut(putNoWitnessTx tx)
 assert "actual native child signature over measured-root environment"(R.verify(R.bytesFromInt(R.xOnly child))(w256ToBytes message)signature)
 assert "actual derived Taproot payout private/public relation"(R.pointMul R.gPt outputSecret==Just output)
 parsed<-either fail return(parseRawTx raw)
 assert "canonical base wire and every raw input outpoint"(runPut(putNoWitnessTx(rawToSigTx parsed))==raw&&and[case(riOutpoint a,sigTxiPreviousOutpoint b)of(Outpoint h i,Outpoint expected j)->hashToBytes h==hashToBytes expected&&i==j|(a,b)<-zip(rtIns parsed)(V.toList(sigTxIn tx))])
 let values=[("measured_cmr",hashToBytes cmr),("actual_funding_script",fundingScript(defaultTap cmr)),("actual_payout_script",H.payoutScript child),("native_sig_all_hash",w256ToBytes message),("child_signature64",signature),("unsigned_base_transaction",raw)]
 writeFile "vendor-specs/bitcoin-growth6/hd-wallet-measured-wire.tsv"("field\thex_value\n"++concat[k++"\t"++hex v++"\n"|(k,v)<-values])
