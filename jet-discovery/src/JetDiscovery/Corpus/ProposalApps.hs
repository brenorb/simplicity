{-# LANGUAGE RankNTypes #-}
-- | Published transaction-policy applications with their expensive path in
-- the spend: custom signature hashes, bounded fee sums, oracle signatures and
-- an elliptic-curve point lock. No Elements primitive is imported.
module JetDiscovery.Corpus.ProposalApps (entries) where
import Prelude hiding (drop,take,not,and,or)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Word as DW
import Data.Serialize (runPut,putWord32be)
import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as S
import Simplicity.Bitcoin.Term (Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SH
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.LibSecp256k1.Schnorr (Sig(..))
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (sigMsg,checkSigWith)
import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer (ctxWith)
import JetDiscovery.Lib.State
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as R

type SigW=(Word256,Word256)
skOwner=71;skRecipient=83;skOracle=97
pk sk=w256 (R.pubkeyOf sk)
recipient i=unhex "0014"<>BS.replicate 20 (fromIntegral (0xe0+i))
script=unhex "5120"<>BS.replicate 32 0xef
scriptHash=w256FromBytes . hashToBytes . sha256
sigW (Sig r s)=(w256 (toInteger r),w256 (toInteger s))
zeroSig=(w256 0,w256 0)
add64 a b=(a&&&b)>>>A.add word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
sub64 a b=(a&&&b)>>>A.subtract word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
same a b=(a&&&b)>>>eq>>>verify
outVal i=konst (w32 i)>>>primitive P.OutputValue>>>verify
outScript i=konst (w32 i)>>>primitive P.OutputScriptHash>>>verify
count n=same (unit>>>Tx.numOutputs) (konst (w32 n))
pay i dest amount=(same (outScript i) (konst (scriptHash dest))&&&same (outVal i) amount)>>>unit
-- Bounded sums include every input; NumInputs is checked before summing.
inputSum :: (Assert t,Primitive t) => t () Word64
inputSum=L.foldl' (\acc i->(konst (w32 i)>>>primitive P.InputValue)&&&acc>>>match ih (add64 oh ih)) (konst (w64 0)) [0..7]
inputBound :: (Assert t,Primitive t) => t () ()
inputBound=(Tx.numInputs&&&konst (w32 8))>>>A.le word32>>>verify
fee :: (Assert t,Primitive t) => t () Word64
fee= sub64 inputSum (add64 (outVal 0) (outVal 1))

-- Custom NIFB signature commits input authorization, first payment and both
-- scripts. It deliberately excludes nLockTime and the change amount.
nifbHash :: (Assert t,Primitive t) => t () Word256
nifbHash=ctx8InitTag "Simplicity/NIFB"
 >>>ctxWith (primitive P.Version) ctx8Add4
 >>>ctxWith SH.inputsHash ctx8Add32
 >>>ctxWith SH.inputUtxosHash ctx8Add32
 >>>ctxWith (konst (w32 0)>>>SH.outputHash>>>verify) ctx8Add32
 >>>ctxWith SH.outputScriptsHash ctx8Add32
 >>>ctxWith SH.tapEnvHash ctx8Add32
 >>>ctxWith (primitive P.CurrentIndex) ctx8Add4
 >>>ctx8Finalize

nifb :: (Simplicity t,Primitive t) => SigW -> t () ()
nifb signature=(count 2&&&inputBound&&&checkSigWith (pk skOwner) nifbHash (witness signature)&&&feeOk)>>>unit
 where
  elapsed=((TL.txLockTime&&&konst (w32 1800000000))>>>A.subtract word32)>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
  maximumFee=add64 (konst (w64 1000)) (konst (w32 0)&&&elapsed)
  feeOk=(fee&&&maximumFee)>>>A.lt word64>>>verify

-- Exact price+height bytes from the published HODL-vault example; no claim
-- that nLockTime can authenticate the current chain tip or an upper time bound.
hodl :: (Simplicity t,Primitive t) => ((Word32,Word32),(SigW,SigW)) -> t () ()
hodl w=witness w>>>hodlT
hodlT :: (Simplicity t,Primitive t) => t ((Word32,Word32),(SigW,SigW)) ()
hodlT=(minimumHeight&&&heightGate&&&priceGate&&&oracle&&&owner)>>>unit
 where
  h=take oh;p=take ih
  minimumHeight=(konst (w32 850000)&&&h)>>>A.le word32>>>verify
  heightGate=h>>>TL.checkLockHeight
  priceGate=(konst (w32 100000)&&&p)>>>A.le word32>>>verify
  msg=(((unit>>>ctx8Init)&&&h>>>ctx8Add4)&&&p)>>>ctx8Add4>>>ctx8Finalize
  oracle=checkSigWith (pk skOracle) msg (drop oh)
  owner=checkSigWith (pk skOwner) (unit>>>sigMsg) (drop ih)

-- A complete PTLC lock: receiver reveals t such that tG=T and signs the spend;
-- sender recovers after expiry. Both point generation and normalization run.
pointLock :: (Simplicity t,Primitive t) => Either (Word256,SigW) SigW -> t () ()
pointLock w=witness w&&&sigMsg>>>match claim timeout
 where
  claim=(canonical&&&pointOk&&&checkSigWith (pk skRecipient) ih oih)>>>unit
  scalar=take oh
  canonical=((scalar&&&konst (w256 R.n))>>>A.lt word256>>>verify)&&&((scalar&&&konst (w256 0))>>>eq>>>not iden>>>verify)>>>unit
  pointOk=((scalar>>>S.generate>>>S.gej_normalize>>>verify)&&&konst pointT)>>>eq>>>verify
  timeout=(unit>>>konst (w32 900000)>>>TL.checkLockHeight)&&&checkSigWith (pk skOwner) ih oh>>>unit
  Just (tx,ty)=R.pointMul R.gPt 313
  pointT=(w256 tx,w256 ty)

-- Payjoin on-chain spend-policy subset: original sender payment/change are
-- protected, the added input's entire value reaches the receiver, and the fee
-- increase is bounded. PSBT metadata/finalization checks remain wallet-side.
payjoin :: (Simplicity t,Primitive t) => SigW -> t () ()
payjoin signature=(count 2&&&twoInputs&&&owner&&&unchanged&&&payment&&&change&&&feeBounds)>>>unit
 where
  twoInputs=same Tx.numInputs (konst (w32 2))
  owner=checkSigWith (pk skOwner) sigMsg (witness signature)
  unchanged=same (primitive P.Version) (konst (w32 2))&&&same (primitive P.LockTime) (konst (w32 0))&&&same Tx.currentSequence (konst (w32 0xfffffffe))>>>unit
  extra=konst (w32 1)>>>primitive P.InputValue>>>verify
  payment=(same (outScript 0) (konst (scriptHash (recipient 0)))&&&((add64 (konst (w64 50000)) extra&&&outVal 0)>>>A.le word64>>>verify))>>>unit
  change=(same (outScript 1) (konst (scriptHash (recipient 1)))&&&((konst (w64 48500)&&&outVal 1)>>>A.le word64>>>verify))>>>unit
  feeBounds=((konst (w64 1000)&&&fee)>>>A.le word64>>>verify)&&&((fee&&&konst (w64 1500))>>>A.le word64>>>verify)>>>unit

-- ACP message authenticates this input, all outputs and the local Taproot
-- environment, while permitting other pledged inputs to be inserted/reordered.
acpHash :: (Assert t,Primitive t) => t () Word256
acpHash=ctx8InitTag "Simplicity/Crowdfund/ACP"
 >>>ctxWith (primitive P.Version) ctx8Add4
 >>>ctxWith (primitive P.LockTime) ctx8Add4
 >>>ctxWith Tx.currentPrevOutpoint ctxOutpoint
 >>>ctxWith Tx.currentValue ctx8Add8
 >>>ctxWith Tx.currentScriptHash ctx8Add32
 >>>ctxWith Tx.currentSequence ctx8Add4
 >>>ctxWith SH.outputsHash ctx8Add32
 >>>ctxWith SH.tapEnvHash ctx8Add32
 >>>ctx8Finalize
 where ctxOutpoint=(((oh&&&ioh)>>>ctx8Add32)&&&iih)>>>ctx8Add4

crowdfund :: (Simplicity t,Primitive t) => (Word256,Either SigW SigW) -> t () ()
crowdfund w=witness w>>>crowdfundT
crowdfundT :: (Simplicity t,Primitive t) => t (Word256,Either SigW SigW) ()
crowdfundT=loadState oh&&&((ih&&&oh)>>>match collect refund)>>>unit
 where
  dynamicSig digest=((ih&&&(unit>>>digest))&&&oh)>>>S.bip_0340_verify
  collect=(dynamicSig acpHash&&&collectChecks)>>>unit
  collectChecks=(count 1&&&(unit>>>inputBound)&&&((konst (w64 150000)&&&(unit>>>inputSum))>>>A.le word64>>>verify)
   &&&pay 0 (recipient 2) (konst (w64 149000))&&&((sub64 (unit>>>inputSum) (outVal 0)&&&konst (w64 1000))>>>A.le word64>>>verify))>>>unit
  refund=(dynamicSig sigMsg&&&refundChecks)>>>unit
  refundChecks=(same (unit>>>Tx.numInputs) (konst (w32 1))&&&count 1&&&(konst (w32 900000)>>>TL.checkLockHeight)
   &&&same (outVal 0) (sub64 (unit>>>Tx.currentValue) (konst (w64 1000)))&&&same (outScript 0) ownerScript)>>>unit
  ownerScript=(((unit>>>ctx8Init)&&&konst (w16 0x5120)>>>ctx8Add2)&&&ih)>>>ctx8Add32>>>ctx8Finalize

baseEnv lock sq value extra outs=mkEnv (mkTx 2 (mkInput (dummyOutpoint 0) (fromInteger value) (BL.fromStrict script) sq:
 [mkInput (dummyOutpoint (fromIntegral i)) (fromInteger v) (BL.fromStrict (recipient i)) sq|(i,v)<-zip [1..] extra]) [mkOutput (fromInteger v) s|(v,s)<-outs] lock) 0 defaultTap
signAll sk prog makeEnv=case makeEnv (progCmr prog)>>=(\e->J.fastEval (unwrap (J.jetSubst SH.sigAllHash)) e ()) of
 Just m->sigW (signMsg sk (w256ToBytes m));_->error "proposal sig-all"

entries :: [Entry]
entries=[nifbEntry,hodlEntry,pointEntry,payjoinEntry,crowdEntry]
 where
  -- Reuse one signature while locktime/change move within the fee policy.
  nifbP sig=Prog (nifb sig)
  nEnv time change dest=baseEnv time 0xfffffffe 100000 [] [(50000,recipient 0),(change,dest)]
  nBase=nEnv 1800000001 49000 (recipient 1)
  nCmr=progCmr (nifbP zeroSig)
  nSig=case nBase nCmr>>=(\e->J.fastEval (unwrap (J.jetSubst nifbHash)) e ()) of Just m->sigW (signMsg skOwner (w256ToBytes m));_->error "NIFB message"
  nifbEntry=Entry "app-noninteractive-fee-bump" "Noninteractive linear-time fee bump with reusable signature" "Pinned SimplicityHL examples/non_interactive_fee_bump.simf; Bitcoin bounded fee-sum adaptation"
   BitcoinApp (Derived "one signature is reused after actual nLockTime/change modifications; full input/output amounts inspected")
   ["two outputs, at most8inputs; first payment and both scripts are signed, nLockTime/change amount are not", "fee<1000+(txLockTime-1800000000); declared locktime is enforced by Bitcoin consensus; no claim about current block time", "Bitcoin fee is a checked sum of input values minus both outputs; no Elements fee primitive"]
   (\sig->nifbP sig)
   [Vector "original fee1000" nBase nSig Accept,
    Vector "same signature, later locktime permits fee1499" (nEnv 1800000500 48501 (recipient 1)) nSig Accept,
    Vector "same signature, fee at strict upper bound" (nEnv 1800000500 48500 (recipient 1)) nSig Reject,
    Vector "change script altered" (nEnv 1800000500 48501 otherScript) nSig Reject,
    Vector "before broadcast lower bound" (nEnv 1799999999 49000 (recipient 1)) nSig Reject]
  otherScript=unhex "0014"<>BS.replicate 20 0x22
  -- Published HODL vault with an oracle-signed lower height bound.
  hodlP w=Prog (hodl w)
  hEnv h=baseEnv h 0xfffffffe 100000 [] [(99000,recipient 0)]
  hW height price signHeight signPrice e=((w32 height,w32 price),(oracle,owner))
   where
    oracle=sigW (signMsg skOracle (hashToBytes (sha256 (runPut (putWord32be (fromInteger signHeight)>>putWord32be (fromInteger signPrice))))))
    owner=signAll skOwner (hodlP ((w32 0,w32 0),(zeroSig,zeroSig))) e
  hodlEntry=Entry "app-hodl-price-vault" "HODL vault with signed price and height plus owner authorization" "Pinned SimplicityHL examples/hodl_vault.simf (Bitcoin adaptation)"
   BitcoinApp (Derived "oracle signs exact height_be32||price_be32; owner signs actual transaction; independent boundary fixtures")
   ["oracle report height>=850000 and price>=100000; txLockHeight>=oracleHeight", "reports have a lower bound, not a current-tip freshness guarantee; owner signature is also required"]
   (\w->hodlP w)
   [Vector "price reaches threshold" (hEnv 860000) (hW 860000 100000 860000 100000 (hEnv 860000)) Accept,
    Vector "price too low, signed" (hEnv 860000) (hW 860000 99999 860000 99999 (hEnv 860000)) Reject,
    Vector "report too old" (hEnv 860000) (hW 849999 100000 849999 100000 (hEnv 860000)) Reject,
    Vector "transaction before report height" (hEnv 859999) (hW 860000 100000 860000 100000 (hEnv 859999)) Reject,
    Vector "price changed after oracle signing" (hEnv 860000) (hW 860000 100001 860000 100000 (hEnv 860000)) Reject]
  -- Whole point-time-locked output, not merely a scalar-multiplication kernel.
  pointP w=Prog (pointLock w)
  pEnv h=baseEnv h 0xfffffffe 100000 [] [(99000,recipient 0)]
  pointSig sk e=signAll sk (pointP (Right zeroSig)) e
  pointEntry=Entry "app-point-time-locked-payment" "Whole PTLC receiver secret-point claim and sender timeout" "Schnorr point-lock/adaptor deployment pattern for PTLCs https://github.com/BlockstreamResearch/scriptless-scripts/blob/master/md/multi-hop-locks.md; point-lock algebra tG=T"
   BitcoinApp (Derived "fixed adaptor point313G from Integer curve arithmetic; transaction-bound BIP340 signatures; canonical scalar negatives")
   ["receiver must reveal canonical nonzero scalar t with tG=T and authorize the spend; sender refunds after height900000", "explicit on-chain point lock, not the scriptless MuSig2 wire protocol; point relation is checked in full and off-chain adaptor exchange is outside this output"]
   (\w->pointP w)
   [Vector "receiver claims with correct secret" (pEnv 0) (Left (w256 313,pointSig skRecipient (pEnv 0))) Accept,
    Vector "wrong point secret" (pEnv 0) (Left (w256 314,pointSig skRecipient (pEnv 0))) Reject,
    Vector "noncanonical scalar secret" (pEnv 0) (Left (w256 R.n,pointSig skRecipient (pEnv 0))) Reject,
    Vector "wrong receiver signature" (pEnv 0) (Left (w256 313,pointSig skOwner (pEnv 0))) Reject,
    Vector "sender after timeout" (pEnv 900000) (Right (pointSig skOwner (pEnv 900000))) Accept,
    Vector "sender before timeout" (pEnv 899999) (Right (pointSig skOwner (pEnv 899999))) Reject]
  -- BIP78 scalar fields which a Bitcoin program can observe on chain.
  payjoinP sig=Prog (payjoin sig)
  pjEnv seq payment change dest=baseEnv 0 seq 100000 [20000] [(payment,recipient 0),(change,dest)]
  pj sigEnv=signAll skOwner (payjoinP zeroSig) sigEnv
  payjoinEntry=Entry "app-payjoin-proposal-bounds" "Payjoin sender's on-chain proposal amount/fee policy" "BIP78 sender proposal checklist and maxadditionalfeecontribution (pinned BIP source required); bounded no-output-substitution adaptation"
   BitcoinApp (Derived "receiver adds20000-sat input; sender re-signs even malicious proposals so negatives isolate amount/fee checks")
   ["original payment50000/change49000/fee1000; one appended receiver input; fee contribution<=500; payment substitution disabled", "two inputs/two outputs; version/locktime/sender sequence preserved; sender current input atindex0", "PSBT metadata, original input membership and receiver finalization are wallet-side; this is the complete stated on-chain spending policy"]
   (\sig->payjoinP sig)
   [Vector "receiver adds input and fee500" (pjEnv 0xfffffffe 70000 48500 (recipient 1)) (pj (pjEnv 0xfffffffe 70000 48500 (recipient 1))) Accept,
    Vector "receiver steals one sat of its added input" (pjEnv 0xfffffffe 69999 48501 (recipient 1)) (pj (pjEnv 0xfffffffe 69999 48501 (recipient 1))) Reject,
    Vector "additional fee exceeds cap" (pjEnv 0xfffffffe 70000 48499 (recipient 1)) (pj (pjEnv 0xfffffffe 70000 48499 (recipient 1))) Reject,
    Vector "change script changed" (pjEnv 0xfffffffe 70000 48500 otherScript) (pj (pjEnv 0xfffffffe 70000 48500 otherScript)) Reject,
    Vector "sender sequence changed" (pjEnv 0xfffffffd 70000 48500 (recipient 1)) (pj (pjEnv 0xfffffffd 70000 48500 (recipient 1))) Reject]
  -- Data-committed refund key and an ACP pledge, reusable after inputs insert.
  donor=R.pubkeyOf skOwner
  crowdP w=Prog (crowdfund w)
  crowdCmr=progCmr (crowdP (w256 donor,Left zeroSig))
  crowdEnv inputs index lock out cmr=mkEnv transaction (fromIntegral index) (\_->stateTap cmr (R.bytesFromInt (donors!!index))) cmr
   where
    donors=map R.pubkeyOf [skOwner,skRecipient,skOracle]
    ins=[mkInput (dummyOutpoint (fromIntegral i)) 50000 (BL.fromStrict (stateScript cmr (R.bytesFromInt (donors!!i)))) 0xfffffffe|i<-[0..inputs-1]]
    transaction=mkTx 2 ins [mkOutput (fromInteger (fst out)) (snd out)] lock
  pledged=crowdEnv 1 0 0 (149000,recipient 2)
  pledgeSig=case pledged crowdCmr>>=(\e->J.fastEval (unwrap (J.jetSubst acpHash)) e ()) of Just m->sigW (signMsg skOwner (w256ToBytes m));_->error "pledge signature"
  funded=crowdEnv 3 0 0 (149000,recipient 2)
  refund=crowdEnv 1 0 900000 (49000,unhex "5120"<>R.bytesFromInt donor)
  refundSig=signAll skOwner (crowdP (w256 donor,Right zeroSig)) refund
  crowdEntry=Entry "app-assurance-crowdfunding" "ACP assurance crowdfunding with data-bound donor refund" "Bitcoin assurance-contract construction https://en.bitcoin.it/wiki/Contract#Example_3:_Assurance_contracts; pinned SimplicityHL ACP scope reference"
   BitcoinApp (Derived "one donor signature first signs an underfunded draft, then is reused in a three-input fully funded transaction; owner key committed in internal-key state")
   ["project receives149000 from exactly150000 of inputs with<=1000 fee; at most8inputs; all outputs/current input/Taproot environment are signed but other inputs are not", "each donor may refund its single input after height900000 with a separate sig-all signature", "collection has no upper expiry bound; late collection and a refund may conflict, as in preauthorized assurance transactions; this is not an OP_EXPIRE emulation"]
   (\w->crowdP w)
   [Vector "three pledges fund project, original signature reused" funded (w256 donor,Left pledgeSig) Accept,
    Vector "underfunded draft cannot spend" pledged (w256 donor,Left pledgeSig) Reject,
    Vector "project amount changed" (crowdEnv 3 0 0 (148999,recipient 2)) (w256 donor,Left pledgeSig) Reject,
    Vector "donor refund after timeout" refund (w256 donor,Right refundSig) Accept,
    Vector "refund before timeout" (crowdEnv 1 0 899999 (49000,unhex "5120"<>R.bytesFromInt donor)) (w256 donor,Right (signAll skOwner (crowdP (w256 donor,Right zeroSig)) (crowdEnv 1 0 899999 (49000,unhex "5120"<>R.bytesFromInt donor)))) Reject]
