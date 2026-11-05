{-# LANGUAGE ScopedTypeVariables #-}
-- | RFC 8391 XMSS-SHA2_10_256: full WOTS+ (including checksum), randomized
-- L-tree, and ten randomized Merkle levels, signing Bitcoin sig_all_hash.
module JetDiscovery.Corpus.Xmss (entries, fKernelRef, hKernelRef) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import qualified Data.List as L
import Data.Bits (testBit)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.Word as Word
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Simplicity,Primitive)
import qualified Simplicity.Bitcoin.Jets as Jets
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.Ty.Word
import JetDiscovery.Corpus.Apps (sigMsg)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer (ctxWith)
-- Independent chain/path fields enter once at their consuming stage.
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Xmss as Ref

-- idx, R, WOTS signature, auth path. Public seed/root are fixed script constants.
data W = W Word32 Word256 [Word256] [Word256]
type XmssHeader=(Word32,Word256)
type XmssInput=(XmssHeader,(Word256,Word16))

k32 :: (Core term, TyC a) => Integer -> term a Word32
k32 = konst . toWord32
k256 :: (Core term, TyC a) => Integer -> term a Word256
k256 = konst . toWord256

pick :: (Core term, TyC a, TyC b) => Bool -> term a b -> term (a,a) b
pick True = drop
pick False = take

nibble256 :: Core term => Int -> term Word256 Word4
nibble256 i = pick (testBit i 5) (pick (testBit i 4) (pick (testBit i 3) (pick (testBit i 2) (pick (testBit i 1) (pick (testBit i 0) iden)))))

bit32 :: Core term => Int -> term Word32 Bit
bit32 i = pick (testBit j 4) (pick (testBit j 3) (pick (testBit j 2) (pick (testBit j 1) (pick (testBit j 0) iden))))
 where j=31-i

nib8 :: Core term => term Word4 Word8
nib8 = konst (toWord4 0) &&& iden

addr :: (Core term, TyC a) => Integer -> term a Word32 -> term a Word32 -> term a Word32 -> Integer -> term a Word256
addr typ leaf height node km = ((k32 0 &&& k32 0) &&& (k32 0 &&& k32 typ)) &&& ((leaf &&& height) &&& (node &&& k32 km))

seed :: (Core term, TyC a) => term a Word256
seed = konst (w256FromBytes Ref.publicSeed)

root :: (Core term, TyC a) => term a Word256
root = konst (w256FromBytes Ref.publicRoot)

-- Preserve the input while appending source-dependent 32-byte words.
hashWords :: (Assert term, TyC a) => [term a Word256] -> term a Word256
hashWords ws = (iden &&& (unit >>> ctx8Init)) >>> L.foldl' (>>>) iden [step t | t<-ws] >>> ih >>> ctx8Finalize
 where step t=oh &&& ((ih &&& (oh >>> t)) >>> ctx8Add32)

-- Fixed-width kernels prevent the type-indexed variable-length SHA context
-- from being rebuilt at every WOTS/L-tree call. These match only EXISTING
-- jets, preserve the exact RFC bytes, and introduce no witness fields.
type ThreeWords=(Word256,(Word256,Word256))
type FourWords=((Word256,Word256),(Word256,Word256))

hash3 :: Assert term => term ThreeWords Word256
hash3=(iden &&& (((unit >>> iv) &&& (oh &&& ioh)) >>> hashBlock)) >>>
      ((ih &&& ((oh >>> iih) &&& k256 (2^255+768))) >>> hashBlock)

hash4 :: Assert term => term FourWords Word256
hash4=(iden &&& (((unit >>> iv) &&& oh) >>> hashBlock)) >>>
      ((ih &&& (oh >>> ih)) >>> hashBlock) >>>
      ((iden &&& konst (toWord512 (2^511+1024))) >>> hashBlock)

setKM :: Core term => Integer -> term Word256 Word256
setKM km=oh &&& (ioh &&& (iioh &&& k32 km))

-- RFC 8391 section 5.1: SHA256(toByte(3,32) || SEED || ADRS).
prf :: (Assert term, TyC a) => term a Word256 -> term a Word256
prf ad=ad >>> ((k256 3 &&& (seed &&& iden)) >>> hash3)

fKernelRef :: Assert term => term (Word256,Word256) Word256
fKernelRef=(k256 0 &&& (prf oh &&& ((ih &&& prf (oh >>> setKM 1)) >>> Word.bitwise_xor word256))) >>> hash3

fKernelWrapped :: Jets.WrappedSimplicity (Word256,Word256) Word256
fKernelWrapped=Jets.jetSubst fKernelRef

hKernelRef :: Assert term => term (Word256,(Word256,Word256)) Word256
hKernelRef=((k256 1 &&& prf oh) &&& (masked ioh 1 &&& masked iih 2)) >>> hash4
 where masked t km=(t &&& prf (oh >>> setKM km)) >>> Word.bitwise_xor word256

hKernelWrapped :: Jets.WrappedSimplicity (Word256,(Word256,Word256)) Word256
hKernelWrapped=Jets.jetSubst hKernelRef

-- An address-producing function receives keyAndMask as a fixed code parameter.
fHash :: forall term a. (Simplicity term, TyC a) => (Integer -> term a Word256) -> term a Word256 -> term a Word256
fHash ad msg=(ad 0 &&& msg) >>> unwrap fKernelWrapped

hHash :: forall term a. (Simplicity term, TyC a) => (Integer -> term a Word256) -> term a Word256 -> term a Word256 -> term a Word256
hHash ad l r=(ad 0 &&& (l &&& r)) >>> unwrap hKernelWrapped

-- One monomorphic expression is shared by all 67 WOTS chains. q/i/digit are
-- bound input values, so the shared expression cannot reopen a certificate.
type ChainInput=((Word32,Word32),(Word8,Word256))
chainRef :: forall term. Simplicity term => term ChainInput Word256
chainRef=L.foldl' (>>>) iden [step j|j<-[0..14]] >>> iih
 where
  step j=(((ioh &&& konst (w8 j)) >>> Arith.le word8) &&& iden) >>> cond hashed iden
   where hashed=oh &&& (ioh &&& fHash (\km -> addr 0 ooh oih (k32 j) km) iih)
chainWrapped :: Jets.WrappedSimplicity ChainInput Word256
chainWrapped=Jets.jetSubst chainRef

checksumWord :: forall term. Assert term => term Word256 Word16
checksumWord=(iden &&& konst (toWord16 0)) >>> L.foldl' (>>>) iden [step i|i<-[0..63]] >>> ih
 where step i=oh &&& ((ih &&& (konst (w8 0) &&& ((konst (w8 15) &&& (oh >>> nibble256 i >>> nib8)) >>> Arith.subtract word8 >>> ih))) >>> Arith.add word16 >>> ih)

-- One header witness binds the multiply-used index/randomizer. Independent
-- chain values enter once; each path sibling is bound as data before ordering.
xmss :: forall term. (Simplicity term, Primitive term) => W -> term () ()
xmss (W idxV rV ss authV)=witness (idxV,rV) >>> xmssVerify ss authV

xmssVerify :: forall term. (Simplicity term,Primitive term) => [Word256] -> [Word256] -> term XmssHeader ()
xmssVerify ss authV=(iden &&& msg) >>> (oh &&& (ih &&& (ih >>> checksumWord))) >>> xmssBody ss authV
 where msg=hashWords [k256 2,ih,root,(konst (toWord128 0) &&& (konst (toWord64 0) &&& (k32 0 &&& oh))),unit >>> sigMsg]

xmssBody :: forall term. (Simplicity term,Primitive term) => [Word256] -> [Word256] -> term XmssInput ()
xmssBody ss authV=(indexOk &&& ((treeRoot &&& root) >>> eq >>> verify)) >>> unit
 where
  idx :: term XmssInput Word32
  idx=ooh
  indexOk=(idx &&& k32 1024) >>> Arith.lt word32 >>> verify
  digit :: Int -> term XmssInput Word8
  digit i | i<64=ioh >>> nibble256 i >>> nib8
          | i==64=iih >>> oih >>> nib8
          | i==65=iih >>> ioh >>> nib8
          | otherwise=iih >>> iih >>> nib8
  chain i=((idx &&& k32 (toInteger i)) &&& (digit i &&& witness (ss!!i))) >>> unwrap chainWrapped
  -- RFC8391 Algorithm8 carries the last unpaired endpoint to the next level.
  leaf=ltree 0 [chain i | i<-[0..66]]
  ltree _ [x]=x
  ltree height xs=ltree (height+1) (pairs 0 xs)
   where
    pairs _ []=[]
    pairs _ [x]=[x]
    pairs node (a:b:rest)=hHash (addr 1 idx (k32 height) (k32 node)) a b:pairs (node+1) rest
  treeRoot=(iden &&& leaf) >>> L.foldl' (>>>) iden [level h | h<-[0..9]] >>> ih
  level :: Int -> term (XmssInput,Word256) (XmssInput,Word256)
  level h=(iden &&& witness (authV!!h)) >>> (take oh &&& hashed)
   where
    -- Sibling is bound as data before it is used for BOTH left/right fields.
    parent=take (oh >>> idx >>> Word.shift_const_by false word32 (negate (h+1)))
    ordered=((take (oh >>> idx >>> bit32 h)) &&& (take ih &&& ih)) >>> cond (ih &&& oh) iden
    hashed=hHash (addr 2 (k32 0) (k32 (toInteger h)) parent) (ordered >>> oh) (ordered >>> ih)

entries :: [Entry]
entries = [Entry
  { entryId="pq-xmss-sha2-10-256"
  , entryTitle="Full RFC8391 XMSS-SHA2_10_256 transaction signature"
  , entrySpec="RFC8391 algorithms 3,6,7,8,14 and section 5.1; vendor-specs/eprint/rfc8391.txt"
  , entryCategory=PostQuantum
  , entryVectorSource=Derived "independent ByteString/Integer WOTS+ signer and XMSS verifier in Ref.Xmss; deterministic test key and authentication siblings"
  , entryAssumptions=["n=32, w=16, 67 WOTS+ chains including checksum, height=10", "full randomized SHA-256 key/mask hashes and L-tree; transaction message=sig_all_hash", "fixed public seed/root; signature leaf index is witness and checked <1024", "stateful signing key: application must prevent reuse of a leaf", "derived vectors; no upstream interoperable KAT has yet been checked"]
  , entryProgram = \w -> Prog (xmss w)
  , entryVectors=[Vector "valid signature (reference accepts)" env good Accept,Vector "wrong WOTS chain" env badChain Reject,Vector "wrong Merkle authentication node" env badAuth Reject,Vector "different transaction" env2 good Reject,Vector "leaf index outside height" env badIndex Reject,Vector "same-CMR in-range index splice" env badInRangeIndex Reject,Vector "same-CMR randomizer splice" env badRandomizer Reject]
  }]
 where
  env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xfffffffe] [mkOutput 99000 mempty] 0) 0 defaultTap
  env2=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xfffffffe] [mkOutput 98000 mempty] 0) 0 defaultTap
  cmr=progCmr (Prog (xmss (W (w32 0) (w256 0) (replicate 67 (w256 0)) (replicate 10 (w256 0)))))
  msg=maybe (error "XMSS environment") (\e -> maybe (error "XMSS sighash") w256ToBytes (Jets.fastEval (unwrap (Jets.jetSubst SigHash.sigAllHash)) e ())) (env cmr)
  refSig=Ref.signatureFor msg
  good | Ref.verify msg refSig= W (w32 (Ref.index refSig)) (w256FromBytes (Ref.randomness refSig)) (map w256FromBytes (Ref.chains refSig)) (map w256FromBytes (Ref.auth refSig))
       | otherwise=error "XMSS independent reference rejected its signature"
  badChain=case good of W i r ss ap -> W i r (w256 0:L.drop 1 ss) ap
  badAuth=case good of W i r ss ap -> W i r ss (w256 0:L.drop 1 ap)
  badIndex=case good of W _ r ss ap -> W (w32 1024) r ss ap
  badInRangeIndex=case good of W _ r ss ap -> W (w32 18) r ss ap
  badRandomizer=case good of W i _ ss ap -> W i (w256 0) ss ap
