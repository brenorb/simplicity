{-# LANGUAGE RankNTypes #-}
-- | Complete bounded financial spend predicates. Assets are native BTC
-- collateral; no claim is made to emulate ERC20/ERC1155 or foreign account state.
module JetDiscovery.Corpus.FinancialApps (entries) where
import Prelude hiding (drop,take,not,and,or)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.Word as DW
import Data.Serialize (runPut,putWord64be)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import Simplicity.LibSecp256k1.Schnorr (Sig(..))
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (checkSigWith)
import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as R

type SigW=(Word256,Word256)
keys=[101,202,303] :: [Integer]
pk i=w256 (R.pubkeyOf (keys!!i))
recipient i=unhex "0014"<>BS.replicate 20 (fromIntegral (0xc0+i))
ourScript=unhex "5120"<>BS.replicate 32 0xc9
scriptHash=w256FromBytes . hashToBytes . sha256
sigW (Sig r s)=(w256 (toInteger r),w256 (toInteger s))
attest i tag values=sigW (signMsg (keys!!i) (R.taggedHash tag (BS.replicate 32 0x77<>BS.concat [runPut (putWord64be (fromInteger n))|n<-values])))

outValue :: (Assert t,Primitive t,TyC a) => Integer -> t a Word64
outValue i=konst (w32 i)>>>primitive P.OutputValue>>>verify
outScript :: (Assert t,Primitive t,TyC a) => Integer -> t a Word256
outScript i=konst (w32 i)>>>primitive P.OutputScriptHash>>>verify
pay :: (Assert t,Primitive t,TyC a) => Integer -> Int -> t a Word64 -> t a ()
pay i dest expected=(((outScript i)&&&konst (scriptHash (recipient dest)))>>>eq>>>verify)&&&((outValue i&&&expected)>>>eq>>>verify)>>>unit
count :: (Assert t,Primitive t,TyC a) => Integer -> t a ()
count n=((unit>>>Tx.numOutputs)&&&konst (w32 n))>>>eq>>>verify
add64 a b=(a&&&b)>>>A.add word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
sub64 a b=(a&&&b)>>>A.subtract word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
mulDiv64 a b den=(((a&&&b)>>>A.multiply word64)&&&(konst (w64 0)&&&konst (w64 den)))>>>A.divide word128>>>((oh&&&konst (w64 0)>>>eq>>>verify)&&&ih)>>>ih
report :: (Assert t,TyC a) => String -> [t a Word64] -> t a Word256
report tag values=foldl (\acc x->(acc&&&x)>>>ctx8Add8) ((unit>>>ctx8InitTag tag)&&&konst (w256FromBytes (BS.replicate 32 0x77))>>>ctx8Add32) values>>>ctx8Finalize

env lock sq value outs=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) (fromInteger value) (BL.fromStrict ourScript) sq] [mkOutput (fromInteger v) s|(v,s)<-outs] lock) 0 defaultTap
normalEnv=env 0 0xffffffff 100000

-- Funding-index arithmetic actually runs in the spend, including both signs.
funding :: (Simplicity t,Primitive t) => (Word64,SigW) -> t () ()
funding w=witness w>>>fundingT
fundingT :: (Simplicity t,Primitive t) => t (Word64,SigW) ()
fundingT=(oracle&&&bounds&&&delay&&&count 2&&&pay 0 0 long&&&pay 1 1 short)>>>unit
 where
  ix=oh
  old=konst (w64 1000000)
  oracle=checkSigWith (pk 0) (report "Simplicity/Perpetual/Funding" [ix]) ih
  bounds=((konst (w64 999000)&&&ix)>>>A.le word64>>>verify)&&&((ix&&&konst (w64 1001000))>>>A.le word64>>>verify)>>>unit
  delay=konst (w16 24)>>>TL.checkLockDistance
  delta=sub64 ((old&&&ix)>>>A.max word64) ((old&&&ix)>>>A.min word64)
  payment=mulDiv64 delta (konst (w64 100000007)) 1000000
  long=((old&&&ix)>>>A.le word64)&&&iden>>>cond (sub64 (konst (w64 50000)) payment) (add64 (konst (w64 50000)) payment)
  short=sub64 (konst (w64 99000)) long
fundingRef ix=let payment=abs (ix-1000000)*100000007`div`1000000;long=50000+(if ix>=1000000 then -payment else payment) in [long,99000-long]
fundingW ix=(w64 ix,attest 0 "Simplicity/Perpetual/Funding" [ix])
fundingEnv sq ix=env 0 sq 100000 (zip (fundingRef ix) [recipient 0,recipient 1])

-- Authenticated report includes all observations; the median decides the payout.
medianOracle :: (Simplicity t,Primitive t) => ((Word64,(Word64,Word64)),[SigW]) -> t () ()
medianOracle (prices,[s0,s1,s2])=witness (prices,(s0,(s1,s2)))>>>medianOracleT
medianOracle _=error "three report signatures"
medianOracleT :: (Simplicity t,Primitive t) => t ((Word64,(Word64,Word64)),(SigW,(SigW,SigW))) ()
medianOracleT=(verifyReports&&&count 2&&&pay 0 0 long&&&pay 1 1 short)>>>unit
 where
  price=oh
  digest=report "Simplicity/Oracle/Median" [price>>>oh,price>>>ioh,price>>>iih]
  verifyReports=(checkSigWith (pk 0) digest (drop oh)&&&checkSigWith (pk 1) digest (drop (drop oh))&&&checkSigWith (pk 2) digest (drop (drop ih)))>>>unit
  a=price>>>oh;b=price>>>ioh;c=price>>>iih
  median=((a&&&b)>>>A.min word64)&&&(((a&&&b)>>>A.max word64)&&&c>>>A.min word64)>>>A.max word64
  long=((konst (w64 50000)&&&median)>>>A.le word64)&&&iden>>>cond (konst (w64 70000)) (konst (w64 20000))
  short=sub64 (konst (w64 99000)) long
medianRef [a,b,c]=max (min a b) (min (max a b) c)
medianRef _=error "three observations"
medianW values=let [a,b,c]=values in ((w64 a,(w64 b,w64 c)),[attest i "Simplicity/Oracle/Median" values|i<-[0..2]])
medianEnv xs=normalEnv [(if medianRef xs>=50000 then 70000 else 20000,recipient 0),(if medianRef xs>=50000 then 29000 else 79000,recipient 1)]

-- Fractional binary outcome weights bind a fixed collateral redemption.
conditional :: (Simplicity t,Primitive t) => ((Word64,Word64),SigW) -> t () ()
conditional w=witness w>>>conditionalT
conditionalT :: (Simplicity t,Primitive t) => t ((Word64,Word64),SigW) ()
conditionalT=(oracle&&&normalizes&&&count 2&&&pay 0 0 first&&&pay 1 1 second)>>>unit
 where
  wa=take oh;wb=take ih
  oracle=checkSigWith (pk 0) (report "Simplicity/Conditional/Payout" [wa,wb]) ih
  normalizes=(add64 wa wb&&&konst (w64 1000))>>>eq>>>verify
  first=mulDiv64 (konst (w64 99000)) wa 1000
  second=sub64 (konst (w64 99000)) first
conditionalW a b=((w64 a,w64 b),attest 0 "Simplicity/Conditional/Payout" [a,b])
conditionalEnv a=normalEnv [(99000*a`div`1000,recipient 0),(99000-99000*a`div`1000,recipient 1)]

-- EIP2981 payment splitting adapted to native BTC; three outputs and exact
-- deductions prevent an authorized seller redirecting the royalty.
royalty :: (Simplicity t,Primitive t) => t () ()
royalty=(count 3&&&pay 0 0 feeRoyalty&&&pay 1 1 platform&&&pay 2 2 seller)>>>unit
 where
  feeRoyalty=mulDiv64 (unit>>>Tx.currentValue) (konst (w64 500)) 10000
  platform=mulDiv64 (unit>>>Tx.currentValue) (konst (w64 250)) 10000
  seller=sub64 (sub64 (sub64 (unit>>>Tx.currentValue) feeRoyalty) platform) (konst (w64 1000))
royaltyRef val=[val*500`div`10000,val*250`div`10000,val-val*500`div`10000-val*250`div`10000-1000]
royaltyEnv val=env 0 0xffffffff val (zip (royaltyRef val) [recipient 0,recipient 1,recipient 2])

entries :: [Entry]
entries=
 [Entry "app-perpetual-funding-settlement" "Perpetual cumulative-funding-index collateral settlement" "dYdX-style fundingPayment=positionSize*(newIndex-oldIndex); native BTC collateral adaptation https://docs.dydx.xyz/concepts/trading/funding"
 BitcoinApp (Derived "Integer signed-index arithmetic; tagged BIP340 oracle report; all output values/scripts checked")
 ["one complete bounded settlement path, not an entire perpetual exchange", "previous index1000000 and position100000007 are committed constants; new index in999000..1001000; fixed-point scale10^6", "oracle signs the new index for a fixed32-byte position context; CSV24 delays this UTXO spend, not report age; no timestamp or dynamic funding-period ID is authenticated; collateral100000, fee1000; two payouts"]
 (\w->Prog (funding w))
 [Vector "positive funding" (fundingEnv 24 1000100) (fundingW 1000100) Accept,
  Vector "negative funding" (fundingEnv 24 999900) (fundingW 999900) Accept,
  Vector "zero funding" (fundingEnv 24 1000000) (fundingW 1000000) Accept,
  Vector "settlement too early" (fundingEnv 23 1000100) (fundingW 1000100) Reject,
  Vector "payout altered" (env 0 24 100000 [(40001,recipient 0),(58999,recipient 1)]) (fundingW 1000100) Reject,
  Vector "oracle signature for another index" (fundingEnv 24 1000100) (let (_,s)=fundingW 999900 in (w64 1000100,s)) Reject]
 ,Entry "app-median-oracle-settlement" "Authenticated three-observation median oracle payout" "Chainlink OCR signed-report/median pattern, Schnorr adaptation https://docs.chain.link/architecture-overview/off-chain-reporting"
 BitcoinApp (Derived "three distinct Integer BIP340 signers authenticate the whole report; median and payout from independent Integer arithmetic")
 ["three fixed authorized report signers,3-of-3; BIP340 replaces foreign-chain ECDSA report signatures", "report binds a fixed32-byte context identifier and all three observations; there is no timestamp or dynamic round number, and no latest-feed-state claim; median threshold50000 selects a fixed two-output settlement", "full bounded collateral payout; reporter networking and OCR consensus remain off chain"]
 (\w->Prog (medianOracle w))
 [Vector "median above strike" (medianEnv [40000,60000,70000]) (medianW [40000,60000,70000]) Accept,
  Vector "median below strike" (medianEnv [70000,30000,40000]) (medianW [70000,30000,40000]) Accept,
  Vector "median at strike" (medianEnv [50000,1,90000]) (medianW [50000,1,90000]) Accept,
  Vector "report changed after signing" (medianEnv [40000,60000,70000]) (let (_,s)=medianW [40000,60000,70000] in ((w64 40000,(w64 60001,w64 70000)),s)) Reject,
  Vector "duplicate signer slot" (medianEnv [40000,60000,70000]) (let (p,s)=medianW [40000,60000,70000] in (p,[head s,head s,s!!2])) Reject,
  Vector "wrong payout" (normalEnv [(69999,recipient 0),(29001,recipient 1)]) (medianW [40000,60000,70000]) Reject]
 ,Entry "app-conditional-collateral-redemption" "Fractional binary conditional-collateral redemption" "Gnosis ConditionalTokens redeemPositions payout numerators/denominator; bounded native BTC collateral adaptation (pinned source)"
 BitcoinApp (Derived "oracle signs both payout numerators; Integer proportional split and boundary transactions")
 ["two claimants with committed destinations; oracle weights sum1000; distributable collateral99000 after fixed1000 fee", "consumption of this UTXO prevents a second redemption; transferable ERC1155 claims and foreign condition setup are outside this application"]
 (\w->Prog (conditional w))
 [Vector "fractional resolution" (conditionalEnv 250) (conditionalW 250 750) Accept,
  Vector "first outcome wins" (conditionalEnv 1000) (conditionalW 1000 0) Accept,
  Vector "second outcome wins" (conditionalEnv 0) (conditionalW 0 1000) Accept,
  Vector "invalid normalization, signed" (conditionalEnv 250) (conditionalW 250 751) Reject,
  Vector "wrong payout script" (normalEnv [(24750,recipient 2),(74250,recipient 1)]) (conditionalW 250 750) Reject,
  Vector "one sat short" (normalEnv [(24749,recipient 0),(74251,recipient 1)]) (conditionalW 250 750) Reject]
 ,Entry "app-royalty-payment-splitter" "Native BTC royalty and platform-fee payment splitter" "EIP2981 royaltyInfo proportional royalty plus fixed payment-splitter destinations https://eips.ethereum.org/EIPS/eip-2981"
 BitcoinApp (Derived "Integer basis-point arithmetic on the actual input value; exact three-output covenant and fee subtraction")
 ["one complete payout covenant; royalty5%, platform2.5%, remainder to seller less1000 fee", "asset transfer, token ownership and royalty discovery occur before creating this committed UTXO; no foreign token ledger is implied"]
 (\()->Prog royalty)
 ([Vector ("value "++show val) (royaltyEnv val) () Accept|val<-[100000,123456789,2100000000000000]]++
  [Vector "royalty reduced" (normalEnv [(4999,recipient 0),(2500,recipient 1),(91501,recipient 2)]) () Reject,
   Vector "royalty redirected" (normalEnv [(5000,recipient 2),(2500,recipient 1),(91500,recipient 2)]) () Reject])
 ]
