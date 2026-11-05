module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Data.Serialize(runPut)
import Simplicity.Bitcoin.DataTypes
import JetDiscovery.Tx
import qualified JetDiscovery.Ref.ArkRefresh as A
import qualified JetDiscovery.Ref.ArkRefreshPackage as P
import qualified JetDiscovery.Ref.Bip340 as R
import JetDiscovery.Ref.BitcoinGrowth(le32)
import System.Exit(exitFailure)
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
outpoint(Outpoint h i)=hashToBytes h<>le32(toInteger i)
main=do
 let make height mutation=P.makePackage height(B.replicate 32 0x41)mutation
     good=make 802016 P.Honest
     variants=[P.Honest,P.WrongRoundScript,P.WrongRoundValue,P.WrongNewAmount,P.WrongNodeLink,P.WrongLeafLink,P.WrongForfeitHash,P.WrongForfeitInput,P.WrongLeafOwner]
 assert "all fresh protocol-negative packages have actual valid signatures"(all(P.verifyPackageSignatures.make 802016)variants)
 assert "exact expiry boundary has actual valid signatures"(P.verifyPackageSignatures(make(P.tip+2*P.exitMargin+P.exitDelta)P.Honest))
 parsed<-mapM(either fail return.parseRawTx)(P.wirePackage good)
 let originals=[P.pkgRound good,P.pkgNode good,P.pkgLeaf good,P.pkgForfeit good]
 assert "every parsed input preserves canonical raw outpoint bytes"(and[and[case(riOutpoint rawInput,sigTxiPreviousOutpoint input)of
   (Outpoint h i,Outpoint expected j)->hashToBytes h==hashToBytes expected&&i==j
   |(rawInput,input)<-zip(rtIns raw)(V.toList(sigTxIn original))]|(raw,original)<-zip parsed originals])
 assert "all four exact base no-witness serializations roundtrip"(and[runPut(putNoWitnessTx(rawToSigTx raw))==runPut(putNoWitnessTx original)|(raw,original)<-zip parsed originals])
 case parsed of
  [roundTx,nodeTx,leafTx,forfeitTx]->do
   assert "complete four actual wire transactions"(map rtVersion parsed==[2,3,3,3]&&map(length.rtIns)parsed==replicate 4 1&&map(length.rtOuts)parsed==[2,3,2,2])
   assert "actual R to D link"(outpoint(riOutpoint(head(rtIns nodeTx)))==A.txidBytes(P.pkgRound good)<>le32 0)
   assert "actual D to L link"(outpoint(riOutpoint(head(rtIns leafTx)))==A.txidBytes(P.pkgNode good)<>le32 0)
   assert "actual prior VTXO to F link"(outpoint(riOutpoint(head(rtIns forfeitTx)))==outpoint P.oldPoint)
   assert "exact values and P2A anchors"(map roValue(rtOuts roundTx)==[79000,20000]
     &&map roValue(rtOuts nodeTx)==[49000,30000,0]&&map roValue(rtOuts leafTx)==[49000,0]&&map roValue(rtOuts forfeitTx)==[50000,0]
     &&all((==unhex "51024e73").roScript.last.rtOuts)[nodeTx,leafTx,forfeitTx])
   case rtWitness leafTx of
    [[signature,preimage,script,control]]->do
     let internal=R.intFromBytes(B.take 32(B.drop 1 control))
         sibling=B.drop 33 control
         root=A.tapBranch(A.tapLeaf script)sibling
         t=R.intFromBytes(R.taggedHash "TapTweak"(R.bytesFromInt internal<>root))
         output=R.pointAdd(R.liftX internal)(R.pointMul R.gPt t)
         expectedInput=BL.toStrict(sigTxiScript(sigTxIn(P.pkgLeaf good)V.!0))
         parity=case output of Just(_,y)->if odd y then 1 else 0;_->2
     assert "actual canonical scriptpath witness and Taproot control block"(B.length signature==64&&B.length preimage==32&&B.length script==61&&B.length control==65
       &&B.head control==0xc0+parity&&expectedInput==P.p2tr output
       &&script==A.hashSignScript(hashToBytes(sha256 preimage))(R.xOnly P.newAggregate)
       &&sibling==A.tapLeaf(A.timelockScript 802016(R.pubkeyOf P.serverSecret)))
    _->assert "leaf witness stack shape"False
  _->fail "four certificate transactions"
 writeFile "vendor-specs/bitcoin-growth3/hark-derived-package.tsv"("role\traw_signed_transaction\n"++concat[role++"\t"++hex raw++"\n"|(role,raw)<-zip["round","node","leaf","forfeit"](P.wirePackage good)])
 writeFile "vendor-specs/bitcoin-growth3/hark-derived-context.tsv"("kind\tvalue\ntrusted_tip\t800000\nexit_margin\t144\nold_exit_delta\t144\nnew_expiry\t802016\nround_input_sat\t100000\nnew_tree_sat\t79000\nold_vtxo_sat\t50000\nrequested_new_vtxo_sat\t49000\nother_vtxo_sat\t30000\n")
