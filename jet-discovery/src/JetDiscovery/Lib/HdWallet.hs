{-# LANGUAGE ScopedTypeVariables,RankNTypes #-}
-- | Native BIP32 public-HD withdrawal wallet with exact HMAC-SHA512 CKDpub.
module JetDiscovery.Lib.HdWallet
 (entry,Proof,CKey,ckdPublic,ckdFromDigest,walletKernel) where
import Prelude hiding(drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as S
import qualified Simplicity.Programs.Bitcoin.Lib as Bitcoin
import Simplicity.Bitcoin.Term(Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SH
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.DataTypes(SigTx(..),SigTxInput(..),TapEnv(..))
import Simplicity.LibSecp256k1.Schnorr(PubKey(..))
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.HmacSha512(hmac37)
import JetDiscovery.Lib.BitcoinFunding(fundingScript)
import JetDiscovery.Run(progCmr)
import JetDiscovery.Types
import JetDiscovery.Tx
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.HdWallet as Ref

type GE=(Word256,Word256)
type CKey=(Word8,Word256)
type Sig=(Word256,Word256)
type Proof=(Word32,Sig)
same :: (Assert t,TyC x,TyC y) => t x y -> t x y -> t x()
same a b=(a&&&b)>>>eq>>>verify
parentPoint :: (Assert t,TyC x) => CKey -> t x GE
parentPoint public=konst public>>>(((check&&&iden)>>>ih)>>>(((oh&&&konst(w8 3))>>>eq)&&&ih)>>>S.decompress>>>verify)
 where
  check=((or((oh&&&konst(w8 2))>>>eq)((oh&&&konst(w8 3))>>>eq))>>>verify)
   &&&((ih&&&konst(w256 R.p))>>>A.lt word256>>>verify)>>>unit
ckdFromDigest :: forall t. Assert t => CKey -> t Word512(GE,Word256)
ckdFromDigest public=((((oh&&&konst(w256 R.n))>>>A.lt word256>>>verify)&&&iden)>>>ih)>>>child&&&ih
 where
  child :: t Word512 GE
  child=(((konst(w256 1)&&&(parentPoint public&&&konst(w256 1)))&&&oh)
   >>>S.linear_combination_1>>>S.gej_normalize>>>verify)
ckdPublic :: Simplicity t => Word256 -> CKey -> t Word32(GE,Word256)
ckdPublic chain public=((((iden&&&konst(w32(2^31)))>>>A.lt word32>>>verify)&&&iden)>>>ih)
 >>>(konst chain&&&(konst(fst public)&&&(konst(snd public)&&&iden)))>>>hmac37>>>ckdFromDigest public
keypathOutput :: forall t. Assert t => t GE Word256
keypathOutput=(iden&&&tweak)>>>(check&&&iden)>>>ih
 >>>(((konst(w256 1)&&&((oh>>>evenPoint)&&&konst(w256 1)))&&&ih)>>>S.linear_combination_1>>>S.gej_normalize>>>verify>>>oh)
 where
  tweak :: t GE Word256
  tweak=((unit>>>ctx8InitTag "TapTweak")&&&oh)>>>ctx8Add32>>>ctx8Finalize
  evenPoint :: t GE GE
  evenPoint=(false&&&oh)>>>S.decompress>>>verify
  check :: t(GE,Word256)()
  check=(ih&&&konst(w256 R.n))>>>A.lt word256>>>verify
p2trHash :: Assert t => t Word256 Word256
p2trHash=(((unit>>>ctx8Init)&&&konst(w16 0x5120))>>>ctx8Add2)&&&iden>>>ctx8Add32>>>ctx8Finalize
walletKernel :: forall t. (Simplicity t,Primitive t) => Word256 -> CKey -> t Proof()
walletKernel chain public=(((oh>>>ckdPublic chain public>>>oh)&&&ih)>>>((authorize&&&policy)>>>unit))
 where
  authorize :: t(GE,Sig)()
  authorize=(((ooh&&&(unit>>>SH.sigAllHash))&&&ih)>>>S.bip_0340_verify)
  policy :: t(GE,Sig)()
  policy=(shape&&&funding&&&same(outputHash)(oh>>>keypathOutput>>>p2trHash)&&&conservation)>>>unit
  outputHash :: t(GE,Sig)Word256
  outputHash=konst(w32 0)>>>primitive Prim.OutputScriptHash>>>verify
  shape :: t(GE,Sig)()
  shape=(same(unit>>>Tx.numInputs)(konst(w32 1))&&&same(unit>>>Tx.numOutputs)(konst(w32 1))
   &&&same(unit>>>primitive Prim.CurrentIndex)(konst(w32 0))
   &&&same(unit>>>primitive Prim.Version)(konst(w32 2))&&&same(unit>>>primitive Prim.LockTime)(konst(w32 0))
   &&&same(konst(w32 0)>>>primitive Prim.InputSequence>>>verify)(konst(w32 0xfffffffe))
   &&&same(konst(w32 0)>>>primitive Prim.InputScriptSigHash>>>verify)(konst(w256FromBytes(hashToBytes(sha256 B.empty))))
   &&&same(konst(w32 0)>>>primitive Prim.InputAnnexHash>>>verify)(konst(Left())))>>>unit
  funding :: t(GE,Sig)()
  funding=(same(unit>>>primitive Prim.InternalKey)(konst(w256 R.nums))
   &&&((konst(w8 0)>>>primitive Prim.Tappath>>>isSome>>>not iden)>>>verify)
   &&&same(konst(w32 0)>>>primitive Prim.InputScriptHash>>>verify)
    (((konst(w256 R.nums)&&&(unit>>>SH.tapleafHash))>>>Bitcoin.buildTaptweak)>>>p2trHash))>>>unit
  conservation :: t(GE,Sig)()
  conservation=(same(konst(w32 0)>>>primitive Prim.InputValue>>>verify)
   ((((konst(w32 0)>>>primitive Prim.OutputValue>>>verify)&&&konst(w64 1000))>>>A.add word64)
    >>>((oh>>>not iden>>>verify)&&&ih)>>>ih)
   &&&((konst(w64 0)&&&(konst(w32 0)>>>primitive Prim.OutputValue>>>verify))>>>A.lt word64>>>verify))>>>unit
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
entry :: IO Entry
entry=do
 rows<-map fields.P.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth6/bip32-wallet-derived.tsv"
 let first=rows!!0
     parent=unhex(first!!1);chain=w256FromBytes(unhex(first!!2));public=(w8(toInteger(B.head parent)),w256FromBytes(B.tail parent))
     program=boundProgram(walletKernel chain public)
     cmr=progCmr(program(w32 0,(w256 0,w256 0)))
     params row=(read(row!!0),R.intFromBytes(unhex(row!!6)))
     (i0,k0)=params first;(i1,k1)=params(rows!!1);(imax,kmax)=params(rows!!2);(ihard,khard)=params(rows!!3)
     output secret=R.xOnly(Ref.keypathOutput(R.pointMul R.gPt secret))
     make index secret destination inputValue outputValue lock badFunding badInternal corrupt=
      let base=Ref.walletTx cmr destination inputValue outputValue lock
          tap root=if badInternal then(defaultTap root){tapInternalKey=PubKey(fromInteger(R.pubkeyOf 17))}else defaultTap root
          tx=base{sigTxIn=V.map(\input->if badFunding then input{sigTxiTxo=mkOutput inputValue(unhex "5120"<>R.bytesFromInt(R.pubkeyOf 99))}
                    else if badInternal then input{sigTxiTxo=mkOutput inputValue(fundingScript(tap cmr))}else input)(sigTxIn base)}
          environment root=if root==cmr then mkEnv tx 0 tap root else Nothing
          message=case environment cmr >>= \env->J.fastEval(J.unwrap(J.jetSubst SH.sigAllHash))env()of Just m->w256ToBytes m;_->error "HD native message"
          signature=R.sign secret message(B.replicate 32 0)
          proof=(w32 index,(w256FromBytes(B.take 32 signature),if corrupt then w256 R.n else w256FromBytes(B.drop 32 signature)))
      in(environment,proof)
     vector name fixture expected=Vector name(fst fixture)(snd fixture)expected
     good index secret=make index secret(output secret)100000 99000 0 False False False
 return(Entry "app-bip32-public-hd-withdrawal" "Native BIP32 public-HD withdrawal: exact HMAC-SHA512 child, actual transaction signature and derived Taproot payout"
  "BIP32 BSD2 pinned a0c977f3755da6476b955677ca9318334a2432c4 CKDpub; BIP341 empty-tree TapTweak; RFC2104 HMAC-SHA512"
  BitcoinApp(Derived "Published BIP32 vector2 master/child0; derived index1/max/hardened-formula cases, actual NUMS+program funding and freshly signed bad native transactions; complete all50source key inventory")
  ["NATIVE SPEND: one unknown-log NUMS/internal-key single-leaf wallet UTXO; actual input script must equal its computed Taproot funding script; no sibling leaves/keypath secret",
   "Authenticated root xpub/chaincode is a program constant; one nonhardened child index0..2^31-1, real compressed parent point/prefix, exact37-byte serP||BEindex HMAC-SHA512 and CKDpub point addition",
   "IL>=n and infinity reject; IL0 itself is valid CKDpub if the child point is not infinity; no unchecked digest/point hint is witnessed",
   "Actual child BIP340 signature binds native sig_all_hash; output0 pays the standard empty-tree TapTweak of that same derived child and preserves all collateral minus1000sats; one input/output, positive payout",
   "This is a single ownership-domain HD wallet, not private-key-isolated child delegation: an xpub plus a nonhardened child private key exposes the corresponding parent private key as BIP32 explains; signatures do not reveal that private key",
   "Master seed generation, hardened account setup, Base58Check xpub parsing and secret backup are external authenticated wallet setup; all50published extended-key cases inventoried,16invalid keys rejected by the independent setup decoder",
   "All4source master seeds/13private edges independently stdlib-HMAC reconstructed; all6nonhardened public edges and17pub/private pairs separately checked; parameter/child-index cases add no group",
   "One structured index/signature witness; child point/digest shared only through typed projections; no transaction/environment CMR is frozen to a placeholder"]
  program
  [vector "published source child0 actual native withdrawal"(good i0 k0)Accept,
   vector "derived public child1 actual native withdrawal"(good i1 k1)Accept,
   vector "maximum nonhardened index actual native withdrawal"(good imax kmax)Accept,
   vector "fresh signature for forbidden hardened public formula"(good ihard khard)Reject,
   vector "fresh child signature cannot divert beneficiary"(make i0 k0(output k1)100000 99000 0 False False False)Reject,
   vector "fresh child signature cannot change exact fee"(make i0 k0(output k0)100000 98999 0 False False False)Reject,
   vector "child signature slot does not match chosen index"(make i1 k0(output k1)100000 99000 0 False False False)Reject,
   vector "fresh signature cannot override committed lock policy"(make i0 k0(output k0)100000 99000 1 False False False)Reject,
   vector "fresh signature cannot fake actual funding script"(make i0 k0(output k0)100000 99000 0 True False False)Reject,
   vector "fresh signature cannot replace unknown-log internal key"(make i0 k0(output k0)100000 99000 0 False True False)Reject,
   vector "noncanonical final child signature scalar n"(make i0 k0(output k0)100000 99000 0 False False True)Reject])
