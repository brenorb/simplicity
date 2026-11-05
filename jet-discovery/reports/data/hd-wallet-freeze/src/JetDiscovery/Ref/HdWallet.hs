-- | Independent point/Bitcoin-output reference for stdlib-derived BIP32 data.
-- HMAC values come from full source extraction; no native digest hint is trusted.
module JetDiscovery.Ref.HdWallet where
import qualified Data.ByteString as B
import JetDiscovery.Tx
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.SilentPayment as Key
import Simplicity.Bitcoin.DataTypes(TapEnv(..),SigTx(..),SigTxInput(..))
import qualified Data.ByteString.Lazy as BL
import JetDiscovery.Lib.BitcoinFunding(fundingScript)

deriveFromDigest parent digest
 |B.length digest/=64||R.intFromBytes(B.take 32 digest)>=R.n=Nothing
 |otherwise=do
  p<-Key.decodeCompressed parent
  q<-R.pointAdd(Just p)(R.pointMul R.gPt(R.intFromBytes(B.take 32 digest)))
  Just(q,B.drop 32 digest)
keypathOutput child=let internal=R.xOnly child;t=R.intFromBytes(R.taggedHash "TapTweak"(R.bytesFromInt internal))
                   in if t>=R.n then Nothing else R.pointAdd(R.liftX internal)(R.pointMul R.gPt t)
payoutScript child=case keypathOutput child of Just p->unhex "5120"<>R.bytesFromInt(fst p);_->error "invalid BIP341 output"
walletTx root outputKey inputValue outputValue lock=mkTx 2
 [mkInput(dummyOutpoint 0)inputValue(BL.fromStrict(fundingScript(defaultTap root)))0xfffffffe]
 [mkOutput outputValue(unhex "5120"<>R.bytesFromInt outputKey)]lock
