-- | Derived complete two-leaf current Bark hArk completion certificates.
-- All signing secrets/nonces are public test fixtures. Only local code runs.
module JetDiscovery.Ref.ArkRefreshPackage where
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Simplicity.Bitcoin.DataTypes
import JetDiscovery.Tx
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.ArkRefresh as A
import JetDiscovery.Ref.SilentPayment(compressed)

serverSecret=37;oldUserSecret=23;newUserSecret=29;otherUserSecret=41;liquiditySecret=43
cosignSecrets=[11,17,31]
exitDelta=144;tip=800000;exitMargin=144
oldValue=50000;newValue=49000;otherValue=30000;roundValue=100000;changeValue=20000
oldPoint=Outpoint(hashFromInteger 0xa2c0001)0
fundingPoint=Outpoint(hashFromInteger 0xa2c0002)1
pub=R.pointMul R.gPt
aggregate secrets=A.keyAgg(map(compressed.pub)secrets)
nodeAggregate=aggregate cosignSecrets
oldAggregate=aggregate[oldUserSecret,serverSecret]
newAggregate=aggregate[newUserSecret,serverSecret]
otherAggregate=aggregate[otherUserSecret,serverSecret]
oldExitLeaves=[A.delayedScript exitDelta(R.pubkeyOf oldUserSecret)]
newExitLeaves=[A.delayedScript exitDelta(R.pubkeyOf newUserSecret)]
oldExit=A.pubkeyPolicy(pub oldUserSecret)(pub serverSecret)exitDelta
newExit=A.pubkeyPolicy(pub newUserSecret)(pub serverSecret)exitDelta
fundingOutput=A.tapOutput(pub liquiditySecret)[]
serverOutput=A.tapOutput(pub serverSecret)[]
otherHash=hashToBytes(sha256(B.replicate 32 0xb2))
p2tr p=unhex "5120"<>R.bytesFromInt(R.xOnly p)
anchor=mkOutput 0(unhex "51024e73")
outpoint tx index=Outpoint(hashFromBytes(A.txidBytes tx))index

data Mutation=Honest|WrongRoundScript|WrongRoundValue|WrongNewAmount|WrongNodeLink|WrongLeafLink
 |WrongForfeitHash|WrongForfeitInput|WrongLeafOwner deriving(Eq,Show)
data Package=Package
 {pkgHeight::Integer,pkgPreimage::B.ByteString,pkgRound::SigTx,pkgNode::SigTx,pkgLeaf::SigTx,pkgForfeit::SigTx
 ,pkgSignatures::[B.ByteString],pkgLeafScript::B.ByteString,pkgLeafControl::B.ByteString}
makePackage height preimage mutation=Package height preimage roundTx nodeTx leafTx forfeitTx signatures leafScript control
 where
  hash=hashToBytes(sha256 preimage)
  expiryScript=A.timelockScript height(R.pubkeyOf serverSecret)
  nodeOutput=A.tapOutput nodeAggregate[expiryScript]
  actualNodeOutput=if mutation==WrongRoundScript then pub 99 else nodeOutput
  amount=newValue+if mutation==WrongNewAmount then 1 else 0
  actualRoundValue=roundValue-if mutation==WrongRoundValue then 1 else 0
  change=changeValue-(amount-newValue)
  newLeaf=A.harkLeafPolicy(pub newUserSecret)(pub serverSecret)height hash
  otherLeaf=A.harkLeafPolicy(pub otherUserSecret)(pub serverSecret)height otherHash
  roundTx=mkTx 2[mkInput fundingPoint(fromInteger actualRoundValue)(BL.fromStrict(p2tr fundingOutput))0xfffffffe]
   [mkOutput(fromInteger(amount+otherValue))(p2tr actualNodeOutput),mkOutput(fromInteger change)(p2tr serverOutput)]0
  nodePoint=if mutation==WrongNodeLink then dummyOutpoint 7 else outpoint roundTx 0
  nodeTx=mkTx 3[mkInput nodePoint(fromInteger(amount+otherValue))(BL.fromStrict(p2tr actualNodeOutput))0]
   [mkOutput(fromInteger amount)(p2tr newLeaf),mkOutput(fromInteger otherValue)(p2tr otherLeaf),anchor]0
  leafPoint=if mutation==WrongLeafLink then dummyOutpoint 8 else outpoint nodeTx 0
  actualNewExit=if mutation==WrongLeafOwner then pub 97 else newExit
  leafTx=mkTx 3[mkInput leafPoint(fromInteger amount)(BL.fromStrict(p2tr newLeaf))0]
   [mkOutput(fromInteger amount)(p2tr actualNewExit),anchor]0
  forfeitHash=if mutation==WrongForfeitHash then hashToBytes(sha256(B.replicate 32 0x77))else hash
  forfeitOutput=A.harkForfeitPolicy(pub oldUserSecret)(pub serverSecret)exitDelta forfeitHash
  ffPoint=if mutation==WrongForfeitInput then dummyOutpoint 9 else oldPoint
  forfeitTx=mkTx 3[mkInput ffPoint(fromInteger oldValue)(BL.fromStrict(p2tr oldExit))0xffffffff]
   [mkOutput(fromInteger oldValue)(p2tr forfeitOutput),anchor]0
  leafScript=A.hashSignScript hash(R.xOnly newAggregate)
  leafSibling=A.tapLeaf expiryScript
  parity=case newLeaf of Just(_,y)->if odd y then 1 else 0;_->error "hArk infinite leaf"
  control=B.singleton(0xc0+parity)<>R.bytesFromInt(R.xOnly newAggregate)<>leafSibling
  nodeSecret=if mutation==WrongRoundScript then 99 else A.tapSecret(A.keyAggSecret cosignSecrets)[expiryScript]
  signatures=[sign(A.tapSecret liquiditySecret[])(A.defaultMessage roundTx 0 Nothing),
    sign nodeSecret(A.defaultMessage nodeTx 0 Nothing),
    sign(A.keyAggSecret[newUserSecret,serverSecret])(A.defaultMessage leafTx 0(Just(A.tapLeaf leafScript))),
    sign(A.tapSecret(A.keyAggSecret[oldUserSecret,serverSecret])oldExitLeaves)(A.defaultMessage forfeitTx 0 Nothing)]
  sign secret message=R.sign secret message(B.replicate 32 0)
wirePackage p=zipWith A.wireTx[pkgRound p,pkgNode p,pkgLeaf p,pkgForfeit p]
 [[[sigs!!0]],[[sigs!!1]],[[sigs!!2,pkgPreimage p,pkgLeafScript p,pkgLeafControl p]],[[sigs!!3]]]
 where sigs=pkgSignatures p
verifyPackageSignatures p=and(zipWith3 R.verify public messages(pkgSignatures p))
 where
  outputKey tx=let script=BL.toStrict(sigTxiScript(sigTxIn tx V.!0))in B.drop 2 script
  public=[outputKey(pkgRound p),outputKey(pkgNode p),R.bytesFromInt(R.xOnly newAggregate),outputKey(pkgForfeit p)]
  messages=[A.defaultMessage(pkgRound p)0 Nothing,A.defaultMessage(pkgNode p)0 Nothing,
   A.defaultMessage(pkgLeaf p)0(Just(A.tapLeaf(pkgLeafScript p))),A.defaultMessage(pkgForfeit p)0 Nothing]
