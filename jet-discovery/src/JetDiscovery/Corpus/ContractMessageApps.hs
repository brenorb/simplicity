{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Wire-authenticated messages driving native collateral state transitions.
module JetDiscovery.Corpus.ContractMessageApps where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as H
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import Data.Bits (testBit)
import Data.Serialize (runPut,putWord64le)
import qualified Simplicity.Programs.Word as W
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.LibSecp256k1.Lib as S
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import Simplicity.Bitcoin.Term (Simplicity,Primitive)
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SH
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Corpus.Apps (sigMsg)
import JetDiscovery.Corpus.ContractExpansion (ecRecover,keccakFixed)
import JetDiscovery.Corpus.ContractGrowth hiding (entries,program,entry,vector,vectorPayload,signature)
import qualified JetDiscovery.Corpus.ContractGrowth as G
import JetDiscovery.Lib.Bytes
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Keccak as K
import qualified JetDiscovery.Ref.Bip340 as R

type PermitInput=(Input,(Word256,(Word256,(Word256,Bit))))
type PermitW=(GW,(Integer,(Integer,(Integer,Bool))))
phash=K.keccak256 . BC.pack
pw :: (Core t,TyC a) => BS.ByteString -> t a Word256
pw=konst . w256FromBytes
pNonce,pDeadline,pMaximum :: Core t => t PermitInput Word256
pNonce=drop oh
pDeadline=drop (drop oh)
pMaximum=drop (drop (drop oh))
pParity :: Core t => t PermitInput Bit
pParity=drop (drop (drop ih))
nativeAsset=0x0000000000000000000000000000000000000001
domain=phash "JetDiscovery/native Bitcoin Permit2 adapter domain"
tokenType=phash "TokenPermissions(address token,uint256 amount)"
nativeType=phash "NativeTransfer(bytes32 recipientScriptHash)"
permitType=phash "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,NativeTransfer witness)NativeTransfer(bytes32 recipientScriptHash)TokenPermissions(address token,uint256 amount)"
spenderAddress=address (keys H.!! 2)
ownerAddress=address 42
address sk=case R.pointMul R.gPt sk of Just (x,y)->R.intFromBytes (K.keccak256 (R.bytesFromInt x<>R.bytesFromInt y)) `mod`2^160;_->error "address"

-- Each hash result is staged before byte projection into its parent hash.
pTokenRef,pWitnessRef,pEnvelopeRef :: Assert t => t Word256 Word256
pTokenRef=keccakFixed (wordBytes (pw tokenType)++wordBytes (konst (w256 nativeAsset))++wordBytes iden)
pWitnessRef=keccakFixed (wordBytes (pw nativeType)++wordBytes iden)
pEnvelopeRef=keccakFixed ([konst (w8 0x19),konst (w8 1)]++wordBytes (pw domain)++wordBytes iden)
type StructInput=((Word256,Word256),(Word256,Word256))
pStructRef :: Assert t => t StructInput Word256
pStructRef=keccakFixed (wordBytes (pw permitType)++wordBytes ioh++wordBytes (konst (w256 spenderAddress))++wordBytes ooh++wordBytes oih++wordBytes iih)
pTokenWrapped,pWitnessWrapped,pEnvelopeWrapped :: J.WrappedSimplicity Word256 Word256
pTokenWrapped=J.jetSubst pTokenRef
pWitnessWrapped=J.jetSubst pWitnessRef
pEnvelopeWrapped=J.jetSubst pEnvelopeRef
pStructWrapped :: J.WrappedSimplicity StructInput Word256
pStructWrapped=J.jetSubst pStructRef
{-# NOINLINE pTokenWrapped #-}
{-# NOINLINE pWitnessWrapped #-}
{-# NOINLINE pEnvelopeWrapped #-}
{-# NOINLINE pStructWrapped #-}
pDigest :: Simplicity t => t PermitInput Word256
pDigest=((pNonce&&&pDeadline)&&&((pMaximum>>>J.unwrap pTokenWrapped)&&&(take actorDestination>>>J.unwrap pWitnessWrapped)))>>>J.unwrap pStructWrapped>>>J.unwrap pEnvelopeWrapped

permitT :: (Simplicity t,Primitive t) => t PermitInput ()
permitT=allChecks [take base,take twoActor,take (same mode (konst (w8 0))),take (allChecks [same (o i) (k 0)|i<-[2..14]]),signatureOk,take (sigAt 2),nonceOk,maximumOk,bitmapOk,take transition,take (withdraw amount actorDestination)]
 where
  nonceOk=(pNonce&&&konst (w256 64))>>>A.lt word256>>>verify
  nonce64=pNonce>>>iih
  mask=(nonce64&&&k 1)>>>W.left_shift word64 word64
  oldBitmap=take (o 1)
  unused=same ((oldBitmap&&&mask)>>>W.bitwise_and word64) (k 0)
  bitmapOk=allChecks [unused,same (take (n 1)) ((oldBitmap&&&mask)>>>W.bitwise_or word64)]
  maximumOk=((take amount>>>as256 iden)&&&pMaximum)>>>A.le word256>>>verify
  signatureOk=((pDigest&&&((take (G.payload>>>oh))&&&((take (G.payload>>>ih))&&&pParity)))>>>ecRecover)&&&konst (w256 ownerAddress)>>>eq>>>verify
  transition=changes [(0,sub (o 0) amount),(1,n 1),nonce 15]

permitProgram :: (Simplicity t,Primitive t) => PermitW -> t () ()
permitProgram w=witness (permitInput w)>>>permitT
permitInput :: PermitW -> PermitInput
permitInput (g,(nonceValue,(deadline,(maximumValue,parity))))=(encode g,(w256 nonceValue,(w256 deadline,(w256 maximumValue,if parity then Right () else Left ()))))
permitCmr=progCmr (Prog (permitProgram empty))
 where empty=((0,(pad [],pad []),(0,0),(zeroSig,zeroSig)),(0,(0,(0,False))))
{-# NOINLINE permitCmr #-}

inverse x m=go x (m-2) 1
 where go _ 0 a=a;go b e a=go (b*b`mod`m) (e`div`2) (if odd e then a*b`mod`m else a)
ecdsaSign sk z nonceValue=case R.pointMul R.gPt nonceValue of
 Just (x,y)->(x`mod`R.n,((z+(x`mod`R.n)*sk)*inverse nonceValue R.n)`mod`R.n,odd y)
 _->error "ecdsa nonce"
pDigestRef who maximumValue nonceValue deadline=K.keccak256 (BS.pack [0x19,1]<>domain<>struct)
 where
  token=K.keccak256 (tokenType<>R.bytesFromInt nativeAsset<>R.bytesFromInt maximumValue)
  witnessHash=K.keccak256 (nativeType<>hashToBytes (sha256 (recipient who)))
  struct=K.keccak256 (permitType<>token<>R.bytesFromInt spenderAddress<>R.bytesFromInt nonceValue<>R.bytesFromInt deadline<>witnessHash)

permitVector name oldState newState who requested maximumValue nonceValue signedMaximum signedNonce signer expected=Vector name env signed expected
 where
  deadline=2000000000
  digest=pDigestRef (fromInteger who) signedMaximum signedNonce deadline
  (r,s,parity)=ecdsaSign 42 (R.intFromBytes digest) 73
  unsigned=((0,(pad oldState,pad newState),(who,requested),(zeroSig,(w256 r,w256 s))),(nonceValue,(deadline,(maximumValue,parity))))
  cmr=permitCmr
  env=gEnv (pad oldState) (pad newState) 0 (Just (fromInteger who,requested)) 0xfffffffe
  signed=((0,(pad oldState,pad newState),(who,requested),(spenderSig,(w256 r,w256 s))),(nonceValue,(deadline,(maximumValue,parity))))
  spenderSig=case env cmr>>=(\e->J.fastEval (unwrap (J.jetSubst SH.sigAllHash)) e ()) of
   Just msg->sigW (signMsg (keys H.!! signer) (w256ToBytes msg));_->error "permit native spender signature"

permitEntry=Entry "app-permit2-bitmap-transfer" "EIP712 witness-bound native transfer with an unordered nonce bitmap" "Permit2 SignatureTransfer/PermitHash exact witness-transfer hash, native Bitcoin reserve/recipient adapter"
 BitcoinApp (Derived "independent Keccak ABI-word construction and Integer ECDSA, persistent native reserve/nonce state and actual spender transaction signature")
 ["fixed native-asset/domain adapter and fixed owner/spender; signed witness binds the recipient script hash; requested amount may be below the signed maximum", "one nonce word with bit positions0..63 is the supported domain; other positions reject; collateral and bitmap are committed in the current state", "deadline is part of the exact signed digest but its upper-time expiry is unenforced: no authenticated current-clock primitive is assumed", "this is the complete stated native authorization/replay/payout policy, not a claim of full foreign Permit2 expiration or token-allowance equivalence"]
 (boundProgram permitT . permitInput) vectors
 where
  oldState=pad [100000,0]
  next balance bitmap=pad ([balance,bitmap]++replicate 13 0++[1])
  v=permitVector
  vectors=[v "valid witness transfer consumes bit5" oldState (next 99000 32) 0 1000 1000 5 1000 5 2 Accept,
   v "partial signed amount" oldState (next 99500 32) 1 500 1000 5 1000 5 2 Accept,
   v "used nonce cannot be replayed" (pad [100000,32]) (next 99000 32) 0 1000 1000 5 1000 5 2 Reject,
   v "requested amount exceeds maximum" oldState (next 98999 32) 0 1001 1000 5 1000 5 2 Reject,
   v "signed maximum altered" oldState (next 99000 32) 0 1000 1001 5 1000 5 2 Reject,
   v "wrong designated spender" oldState (next 99000 32) 0 1000 1000 5 1000 5 0 Reject,
   v "unsupported nonce bit64" oldState (next 99000 0) 0 1000 1000 64 1000 64 2 Reject]

entries :: [Entry]
entries=[permitEntry,bubbleEntry]

type BubbleInput=(Input,(Word256,(Word64,((Bit,Word256),(Bit,Word256)))))
type BubbleW=(GW,(Integer,(Integer,[(Bool,BS.ByteString)])))
bOwnerNew :: Core t => t BubbleInput Word256
bOwnerNew=drop oh
bNonce :: Core t => t BubbleInput Word64
bNonce=drop (drop oh)
bProof :: Core t => Int -> t BubbleInput (Bit,Word256)
bProof i=drop (drop (drop (if i==0 then oh else ih)))
assetId=phash "initialized native compressed asset0"
assetData=phash "fixed metadata/content digest"
assetCreators=phash "fixed creator list digest"
bytes8le :: (Core t,TyC a) => t a Word64 -> [t a Word8]
bytes8le a=[a>>>pick (testBit i 2) (pick (testBit i 1) (pick (testBit i 0) iden))|i<-[7::Int,6..0]]
bLeaf :: Simplicity t => Bool -> t BubbleInput Word256
bLeaf newer=(ownerKey&&&(delegateKey&&&bNonce))>>>J.unwrap bLeafWrapped
 where
  ownerKey=if newer then bOwnerNew else take (G.payload>>>oh)
  delegateKey=if newer then bOwnerNew else take (G.payload>>>ih)
bLeafRefT :: Assert t => t (Word256,(Word256,Word64)) Word256
bLeafRefT=keccakFixed ([konst (w8 1)]++wordBytes (pw assetId)++wordBytes oh++wordBytes ioh++bytes8le iih++wordBytes (pw assetData)++wordBytes (pw assetCreators))
bLeafWrapped :: J.WrappedSimplicity (Word256,(Word256,Word64)) Word256
bLeafWrapped=J.jetSubst bLeafRefT
{-# NOINLINE bLeafWrapped #-}
keccakNode :: Assert t => t (Bit,(Word256,Word256)) Word256
keccakNode=cond (ih&&&oh) iden>>>keccakFixed (wordBytes oh++wordBytes ih)
keccakNodeWrapped :: J.WrappedSimplicity (Bit,(Word256,Word256)) Word256
keccakNodeWrapped=J.jetSubst keccakNode
{-# NOINLINE keccakNodeWrapped #-}
bRoots :: forall t. Simplicity t => t BubbleInput (Word256,Word256)
bRoots=(iden&&&(bLeaf False&&&bLeaf True))>>>step 0>>>step 1>>>ih
 where
  step :: Int -> t (BubbleInput,(Word256,Word256)) (BubbleInput,(Word256,Word256))
  step i=oh&&&(hash ioh&&&hash iih)
   where hash root=((take (bProof i>>>oh))&&&(root&&&take (bProof i>>>ih)))>>>J.unwrap keccakNodeWrapped
bubbleT :: (Simplicity t,Primitive t) => t BubbleInput ()
bubbleT=allChecks [take base,take twoActor,take (same mode (konst (w8 0))),take (allChecks [same (o i) (k 0)|i<-[6..15]]),authority,rootCheck,take transition,take noCash]
 where
  key=select (is (take actor) (k 0)) (take (G.payload>>>oh)) (take (G.payload>>>ih))
  authority=((key&&&(unit>>>sigMsg))&&&take G.signature)>>>S.bip_0340_verify
  rootCheck=same bRoots ((take (wordFromFields old 1))&&&(take (wordFromFields new 1)))
  transition=changes (nonce 5:[(i,n i)|i<-[1..4]])
bubbleProgram :: (Simplicity t,Primitive t) => BubbleW -> t () ()
bubbleProgram w=witness (bubbleInput w)>>>bubbleT
bubbleInput :: BubbleW -> BubbleInput
bubbleInput (g,(ownerNext,(nonceValue,[(a,x),(b,y)])))=(encode g,(w256 ownerNext,(w64 nonceValue,((bit a,w256FromBytes x),(bit b,w256FromBytes y)))))
 where bit z=if z then Right () else Left ()
bubbleInput _=error "bounded compressed asset depth2"
bubbleCmr=progCmr (Prog (bubbleProgram empty))
 where empty=((0,(pad [],pad []),(0,0),(zeroSig,zeroSig)),(0,(0,[(False,BS.replicate 32 0),(False,BS.replicate 32 0)])))
{-# NOINLINE bubbleCmr #-}
bLeafRef ident ownerKey delegateKey nonceValue=K.keccak256 (BS.singleton 1<>ident<>R.bytesFromInt ownerKey<>R.bytesFromInt delegateKey<>runPut (putWord64le (fromInteger nonceValue))<>assetData<>assetCreators)
bubbleVector name role signer nonceValue corruptProof wrongOutput expected=Vector name env signed expected
 where
  ownerKey=R.pubkeyOf (keys H.!!0);delegateKey=R.pubkeyOf (keys H.!!1);ownerNext=R.pubkeyOf (keys H.!!2)
  leaf0=bLeafRef assetId ownerKey delegateKey 7
  siblings=[bLeafRef (phash ("initialized native compressed asset"++show i)) ownerKey ownerKey 7|i<-[1::Int ..3]]
  sibling1=siblings H.!!0;sibling2=K.keccak256 (siblings H.!!1<>siblings H.!!2)
  oldRoot=K.keccak256 (K.keccak256 (leaf0<>sibling1)<>sibling2)
  newLeaf=bLeafRef assetId ownerNext ownerNext nonceValue
  newRoot=K.keccak256 (K.keccak256 (newLeaf<>sibling1)<>sibling2)
  state root counter=pad ([100000]++hashWords (w256FromBytes root)++[counter])
  oldState=state oldRoot 5;newState=state newRoot 6
  path=[(False,if corruptProof then BS.replicate 32 0 else sibling1),(False,sibling2)]
  unsigned=((0,(oldState,newState),(role,0),(zeroSig,(w256 ownerKey,w256 delegateKey))),(ownerNext,(nonceValue,path)))
  cmr=bubbleCmr
  env=gEnv oldState (if wrongOutput then state oldRoot 6 else newState) 0 Nothing 0xfffffffe
  signed=((0,(oldState,newState),(role,0),(auth,(w256 ownerKey,w256 delegateKey))),(ownerNext,(nonceValue,path)))
  auth=case env cmr>>=(\e->J.fastEval (unwrap (J.jetSubst SH.sigAllHash)) e ()) of
   Just msg->sigW (signMsg (keys H.!!signer) (w256ToBytes msg));_->error "compressed asset authority signature"
bubbleEntry=Entry "app-compressed-asset-transfer" "Keccak compressed-asset ownership and authenticated root replacement" "BubblegumV1 LeafSchema::to_node/transfer_v1 wire schema; native Bitcoin BIP340 ownership/root-state adaptation"
 BitcoinApp (Derived "four actual independently encoded leaf schemas, Keccak tree/root update, little-endian nonce and transaction-bound owner/delegate signatures")
 ["initialized fixed assetID/data/creator hashes; exact169-byte V1 leaf hash; depth2 proof; new delegate equals new owner", "native owner/delegate keys are BIP340 keys; this is not Solana Ed25519 authorization, PDA derivation or the concurrent-tree changelog", "complete stated transfer of an existing initialized asset and native state collateral; no mint/collection plugin/asset-sale program claimed", "one witness includes old/new state, both authority keys, next owner, nonce and all proof operands"]
 (boundProgram bubbleT . bubbleInput)
 [bubbleVector "owner transfers asset" 0 0 7 False False Accept,
  bubbleVector "delegate transfers asset" 1 1 7 False False Accept,
  bubbleVector "nonowner cannot authorize" 0 2 7 False False Reject,
  bubbleVector "owner key cannot impersonate delegate" 1 0 7 False False Reject,
  bubbleVector "nonce differs from authenticated leaf" 0 0 8 False False Reject,
  bubbleVector "changed proof sibling" 0 0 7 True False Reject,
  bubbleVector "output tree retains previous owner" 0 0 7 False True Reject]
