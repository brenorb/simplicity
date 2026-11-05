{-# LANGUAGE ScopedTypeVariables, GADTs #-}
-- | Full RFC8554 LMS_SHA256_M32_H10 / LMOTS_SHA256_N32_W4 transaction verifier.
-- Unlike XMSS this uses short domain-separated plain hash chains and one hash
-- of all chain endpoints; it has no randomized masks or WOTS+ L-tree.
module JetDiscovery.Corpus.Lms (entries, upstreamCertificate, lmotsHashStep, lmotsHashStepRef) where

import Prelude hiding (drop, take, not, and, or)
import qualified Prelude as P
import qualified Data.List as L
import qualified Data.ByteString as BS
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
-- Independent chain/path words enter once at their unique consuming stage.
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Lms as Ref
import qualified JetDiscovery.Ref.Bip340 as Bip340

data W = W Word32 Word256 [Word256] [Word256]
type LmsHeader=(Word32,Word256)

-- Exact55-byte RFC8554 chain message: I16 || q4 || i2 || j1 || tmp32.
-- Packing one padded block avoids constructing1005 separate variable-length
-- SHA contexts. The kernel has one fixed concrete input type and is shared
-- by every chain. It remains an ordinary unjetted reference expression.
type ChainInput=((Word128,Word32),(Word16,(Word8,Word256)))

pack16 :: (Core term,TyC a) => [term a Word8] -> term a Word128
pack16 xs=pack8 (L.take 8 xs) &&& pack8 (L.drop 8 xs)
 where
  pack8 ys=pack4 (L.take 4 ys) &&& pack4 (L.drop 4 ys)
  pack4 ys=pack2 (L.take 2 ys) &&& pack2 (L.drop 2 ys)
  pack2 [a,b]=a &&& b
  pack2 _=error "LMS pack16"

pack64 :: (Core term,TyC a) => [term a Word8] -> term a Word512
pack64 xs=(pack16 (L.take 16 xs) &&& pack16 (L.take 16 (L.drop 16 xs))) &&&
          (pack16 (L.take 16 (L.drop 32 xs)) &&& pack16 (L.drop 48 xs))

-- Local projection helper, matching the non-exported itemsOf pattern in
-- Haskell/Core/Simplicity/Programs/Word.hs; existing source is untouched.
byteItems :: Core term => Word.Vector Word8 b -> [term b Word8]
byteItems SingleV=[iden]
byteItems (DoubleV v)=map take rec ++ map drop rec
 where rec=byteItems v

lmotsHashStep :: forall term. Simplicity term => term ChainInput Word256
lmotsHashStep=unwrap lmotsHashStepWrapped

-- Freeze this shared library expression after matching EXISTING jets once.
-- The raw reference remains exported below; this is a construction-time
-- optimization, not a new jet or a change to SHA256 semantics/cost.
lmotsHashStepWrapped :: Jets.WrappedSimplicity ChainInput Word256
lmotsHashStepWrapped=Jets.jetSubst lmotsHashStepRef

lmotsHashStepRef :: forall term. Assert term => term ChainInput Word256
lmotsHashStepRef=((unit >>> iv) &&& pack64 bytes) >>> hashBlock
 where
  bytes=map (ooh >>>) (byteItems vector16) ++ map (oih >>>) (byteItems vector4) ++
        map (ioh >>>) (byteItems vector2) ++ [iioh] ++
        map (iiih >>>) (byteItems vector32) ++ map (konst.w8) [128,0,0,0,0,0,0,1,184]

-- Compute the67-chain checksum from a single input digest. Carry the digest
-- as data through a unary pipeline instead of reintroducing its entire term
-- for every nibble and every accumulator node.
checksumWord :: forall term. Assert term => term Word256 Word16
checksumWord=(iden &&& konst (w16 0)) >>> L.foldl' (>>>) iden [step i | i<-[0..63]] >>> ih
 where
  step i=oh &&& ((ih &&& (konst (w8 0) &&& ((konst (w8 15) &&& (oh >>> nibble256 i >>> nib8)) >>> Arith.subtract word8 >>> ih))) >>> Arith.add word16 >>> ih)

k32 :: (Core term,TyC a) => Integer -> term a Word32
k32=konst.toWord32

pick :: (Core term,TyC a,TyC b) => Bool -> term a b -> term (a,a) b
pick True=drop
pick False=take

nibble256 :: Core term => Int -> term Word256 Word4
nibble256 i=pick (testBit i 5) (pick (testBit i 4) (pick (testBit i 3) (pick (testBit i 2) (pick (testBit i 1) (pick (testBit i 0) iden)))))

bit32 :: Core term => Int -> term Word32 Bit
bit32 i=pick (testBit j 4) (pick (testBit j 3) (pick (testBit j 2) (pick (testBit j 1) (pick (testBit j 0) iden))))
 where j=31-i

nib8 :: Core term => term Word4 Word8
nib8=konst (toWord4 0) &&& iden

identifier :: (Core term,TyC a) => term a Word128
identifier=konst (toWord128 (Bip340.intFromBytes Ref.identifier))

lms :: forall term. (Simplicity term,Primitive term) => W -> term () ()
lms=lmsWith (toWord128 (Bip340.intFromBytes Ref.identifier)) (w256FromBytes Ref.publicRoot) (ctxWith sigMsg ctx8Add32)

-- Multiply-used q/randomizer enter once as a small header. Each independent
-- chain/path word enters exactly once at its consuming stage, then flows as
-- data. Carrying all67+10proof words through every hash is unnecessary.
lmsWith :: forall term. (Simplicity term,Primitive term) => Word128 -> Word256 -> term Ctx8 Ctx8 -> W -> term () ()
lmsWith identV rootV appendMessage (W qV cV ss path)=witness (qV,cV) >>> lmsVerify identV rootV appendMessage ss path

-- Preserve the input as data while hashing source-dependent fields.
appendT :: (Assert term,TyC a,TyC b) => term a b -> term (Ctx8,b) Ctx8 -> term (a,Ctx8) (a,Ctx8)
appendT field action=oh &&& ((ih &&& (oh >>> field)) >>> action)
hashStart :: (Assert term,TyC a) => term a (a,Ctx8)
hashStart=iden &&& (unit >>> ctx8Init)
hashEnd :: (Assert term,TyC a) => term (a,Ctx8) Word256
hashEnd=drop ctx8Finalize

lmsVerify :: forall term. (Simplicity term,Primitive term) => Word128 -> Word256 -> term Ctx8 Ctx8 -> [Word256] -> [Word256] -> term LmsHeader ()
lmsVerify identV rootV appendMessage ss path=(qOk &&& ((treeRoot &&& konst rootV) >>> eq >>> verify)) >>> unit
 where
  q :: term LmsHeader Word32
  q=oh
  ident :: forall a. TyC a => term a Word128
  ident=konst identV
  qOk=(q &&& k32 1024) >>> Arith.lt word32 >>> verify
  prefix :: forall a. TyC a => Integer -> term a Word32 -> term a (a,Ctx8)
  prefix domain node=hashStart >>> appendT ident ctx8Add16 >>> appendT node ctx8Add4 >>> appendT (konst (w16 domain)) ctx8Add2
  msg :: term LmsHeader Word256
  msg=prefix 0x8181 q >>> appendT ih ctx8Add32 >>> (oh &&& drop appendMessage) >>> hashEnd
  checksum=msg >>> checksumWord
  digit i | i<64=msg >>> nibble256 i >>> nib8
          | i==64=checksum >>> oih >>> nib8
          | i==65=checksum >>> ioh >>> nib8
          | otherwise=checksum >>> iih >>> nib8
  chainKernel :: term ChainInput Word256
  chainKernel=lmotsHashStep
  -- State ((bound q,digit),value): q and digit are values, never new witnesses.
  chain :: Int -> term LmsHeader Word256
  chain i=((q &&& digit i) &&& witness (ss!!i)) >>> L.foldl' (>>>) iden [step j | j<-[0..14]] >>> ih
   where
    step j=(((oih &&& konst (w8 (toInteger j))) >>> Arith.le word8) &&& iden) >>> cond (oh &&& hashed j) iden
    hashed j=((ident &&& ooh) &&& (konst (w16 (toInteger i)) &&& (konst (w8 (toInteger j)) &&& ih))) >>> chainKernel
  publicCandidate=prefix 0x8080 q >>> L.foldl' (>>>) iden [appendT (chain i) ctx8Add32 | i<-[0..66]] >>> hashEnd
  initialNode=(q &&& k32 1024) >>> Arith.add word32 >>> ih
  leaf=prefix 0x8282 initialNode >>> appendT publicCandidate ctx8Add32 >>> hashEnd
  treeRoot=(iden &&& leaf) >>> L.foldl' (>>>) iden [level h | h<-[0..9]] >>> ih
  level :: Int -> term (LmsHeader,Word256) (LmsHeader,Word256)
  level h=iden &&& hashed >>> (take oh &&& ih)
   where
    parent=oh >>> initialNode >>> Word.shift_const_by false word32 (negate (h+1))
    sibling=witness (path!!h)
    ordered=((oh >>> q >>> bit32 h) &&& (ih &&& sibling)) >>> cond (ih &&& oh) iden
    hashed=prefix 0x8383 parent >>> appendT ordered ctx8Add64 >>> hashEnd

entries :: [Entry]
entries=[Entry
 { entryId="pq-lms-sha256-m32-h10"
 , entryTitle="Full RFC8554 LMS height10 with LMOTS SHA256 n32 w4 transaction signature"
 , entrySpec="RFC8554 algorithms 4b and 6a; vendor-specs/eprint/rfc8554.txt"
 , entryCategory=PostQuantum
 , entryVectorSource=Derived "independent ByteString/Integer reference LMOTS signer and LMS verifier in Ref.Lms; deterministic test key"
 , entryAssumptions=["fixed LMS_SHA256_M32_H10 and LMOTS_SHA256_N32_W4, not a generic wire-format decoder", "67 chains including checksum and 10-level authentication path; q<1024 checked", "fixed 16-byte identifier/root and message=sig_all_hash", "stateful signing key; reuse of an OTS leaf must be prevented by the application", "derived transaction vectors; matching RFC8554 appendixF H10/W4 subkey-certificate KAT is checked separately by upstreamCertificate"]
 , entryProgram = \w -> Prog (lms w)
 , entryVectors=[Vector "valid signature (reference accepts)" env good Accept,Vector "corrupted LMOTS chain" env badChain Reject,Vector "corrupted LMS path" env badAuth Reject,Vector "different transaction" env2 good Reject,Vector "out-of-range leaf index" env badIndex Reject,Vector "same-CMR in-range index splice" env badInRangeIndex Reject,Vector "same-CMR randomizer splice" env badRandomizer Reject]
 }]
 where
  env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xfffffffe] [mkOutput 99000 mempty] 0) 0 defaultTap
  env2=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xfffffffe] [mkOutput 98000 mempty] 0) 0 defaultTap
  cmr=progCmr (Prog (lms (W (w32 0) (w256 0) (replicate 67 (w256 0)) (replicate 10 (w256 0)))))
  msg=maybe (error "LMS environment") (\e -> maybe (error "LMS sighash") w256ToBytes (Jets.fastEval (unwrap (Jets.jetSubst SigHash.sigAllHash)) e ())) (env cmr)
  refSig=Ref.signatureFor msg
  good | Ref.verify msg refSig=W (w32 (Ref.leafIndex refSig)) (w256FromBytes (Ref.randomizer refSig)) (map w256FromBytes (Ref.chains refSig)) (map w256FromBytes (Ref.auth refSig))
       | otherwise=error "LMS independent reference rejected its signature"
  badChain=case good of W i r ss ap -> W i r (w256 0:L.drop 1 ss) ap
  badAuth=case good of W i r ss ap -> W i r ss (w256 0:L.drop 1 ap)
  badIndex=case good of W _ r ss ap -> W (w32 1024) r ss ap
  badInRangeIndex=case good of W _ r ss ap -> W (w32 18) r ss ap
  badRandomizer=case good of W i _ ss ap -> W i (w256 0) ss ap

-- A matching H10/W4 upstream KAT. It signs a 56-byte child LMS public key,
-- so it is a separate test fixture rather than a parameter-sweep corpus entry.
upstreamCertificate :: IO Entry
upstreamCertificate=do
  raw<-readFile "vendor-specs/eprint/rfc8554-testcase2-lms.txt"
  let rows=[(k,L.drop 1 v) | line<-lines raw, (k,v)<-[break (=='=') line], P.not (null v)]
      field k=maybe (error ("RFC8554 missing field "++k)) unhex (lookup k rows)
      ident=field "parent_I"
      key=field "parent_K"
      childI=field "child_I"
      childK=field "child_K"
      q=Bip340.intFromBytes (field "q")
      c=field "C"
      ss=[field ("y"++show i) | i<-[0..66]]
      ap=[field ("path"++show i) | i<-[0..9]]
      sg=Ref.Signature q c ss ap
      msg=BS.pack [0,0,0,5,0,0,0,4]<>childI<>childK
      good=W (w32 q) (w256FromBytes c) (map w256FromBytes ss) (map w256FromBytes ap)
      bad=case good of W i r ys path -> W i r (w256 0:L.drop 1 ys) path
      badQ=case good of W _ r ys path -> W (w32 4) r ys path
      badC=case good of W i _ ys path -> W i (w256 0) ys path
      append :: Assert term => term Ctx8 Ctx8
      append=ctxWith (k32 5) ctx8Add4 >>> ctxWith (k32 4) ctx8Add4 >>> ctxWith (konst (toWord128 (Bip340.intFromBytes childI))) ctx8Add16 >>> ctxWith (konst (w256FromBytes childK)) ctx8Add32
      program w=Prog (lmsWith (toWord128 (Bip340.intFromBytes ident)) (w256FromBytes key) append w)
      env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xfffffffe] [mkOutput 99000 mempty] 0) 0 defaultTap
  if P.not (Ref.verifyWith ident key msg sg) then error "RFC8554 upstream KAT rejected by independent reference" else
    pure Entry {entryId="upstream-lms-h10-w4-subkey-certificate",entryTitle="RFC8554 appendixF test case2 subkey certificate",entrySpec="RFC8554 appendixF",entryCategory=PostQuantum,entryVectorSource=Upstream "vendor-specs/eprint/rfc8554-testcase2-lms.txt, extracted by tools/extract_lms_rfc8554.py",entryAssumptions=["upstream KAT only; not counted as another corpus application"],entryProgram=program,entryVectors=[Vector "RFC8554 H10/W4 certificate" env good Accept,Vector "corrupt upstream certificate" env bad Reject,Vector "same-CMR upstream q splice" env badQ Reject,Vector "same-CMR upstream randomizer splice" env badC Reject]}
