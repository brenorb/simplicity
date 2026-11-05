module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Simplicity.Bitcoin.DataTypes
import JetDiscovery.Tx
import qualified JetDiscovery.Ref.ArkRefresh as A
import qualified JetDiscovery.Ref.SilentPayment as S
import qualified JetDiscovery.Ref.Bip340 as R
import System.Exit(exitFailure)
fields delimiter s=case break(==delimiter)s of(a,[])->[a];(a,_:b)->a:fields delimiter b
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
main=do
 [row]<-map(fields '\t').drop 1.lines <$>readFile "vendor-specs/bitcoin-growth3/bark-round-root-kat.tsv"
 case row of
  [server,expiry,expected,secrets]->do
   let keys=map(R.intFromBytes.unhex)(fields ',' secrets)
       public=map(S.compressed.R.pointMul R.gPt)keys
       aggregate=A.keyAgg public
       aggregateSecret=A.keyAggSecret keys
       scripts=[A.timelockScript(read expiry)(R.pubkeyOf(R.intFromBytes(unhex server)))]
       actual=A.tapOutput aggregate scripts
   assert "exact published eight-key Bark round output"(R.bytesFromInt(R.xOnly actual)==unhex expected)
   assert "exact aggregate secret/public relation for fixture"(R.pointMul R.gPt aggregateSecret==aggregate)
   assert "exact TapTweak output secret/public relation"(R.pubkeyOf(A.tapSecret aggregateSecret scripts)==R.xOnly actual)
  _->fail "Bark root KAT columns"
 raw<-unhex.filter(/='\n') <$>readFile "vendor-specs/bitcoin-growth2/bip341-group-0-unsigned.hex"
 utxos<-map(fields '\t').drop 1.lines <$>readFile "vendor-specs/bitcoin-growth2/bip341-group-0-utxos.tsv"
 [kat]<-map(fields '\t').drop 1.lines <$>readFile "vendor-specs/bitcoin-growth3/bip341-default-crosscheck.tsv"
 parsed<-either fail return(parseRawTx raw)
 let tx0=rawToSigTx parsed
     tx=tx0{sigTxIn=V.imap(\i input->case utxos!!i of
        [j,amount,script]|read j==i->input{sigTxiTxo=TxOutput(read amount)(BL.fromStrict(unhex script))}
        _->error "UTXO columns")(sigTxIn tx0)}
 case kat of
  [index,expected,signature]->do
   let i=read index;msg=A.defaultMessage tx i Nothing
       pk=B.drop 2(BL.toStrict(sigTxiScript(sigTxIn tx V.!fromIntegral i)))
   assert "published exact BIP341 DEFAULT digest"(msg==unhex expected)
   assert "published exact BIP341 DEFAULT signature"(R.verify pk msg(unhex signature))
  _->fail "BIP341 default columns"
 assert "exact minimal CSV144 script prefix"(B.take 6(A.delayedScript 144(R.pubkeyOf 11))==unhex "029000b27520")
 assert "exact current hash-and-sign size-guard prefix"(B.take 6(A.hashSignScript(B.replicate 32 1)(R.pubkeyOf 11))==unhex "82012088a914")
