{-# LANGUAGE ScopedTypeVariables, GADTs #-}
-- | Full FIPS205 SLH-DSA-SHA2-128s verification on Bitcoin sig_all_hash.
-- Exact n16,h63,d7,hprime9,k14,a12,w16; standard7856-byte signature,
--32-byte public key and pure external API with empty context (M'=0||0||M).
-- Uses the shared direct WOTS hash kernel and binds each logical witness once.
module JetDiscovery.Corpus.SlhDsaStandard
  ( entries, directWotsChain, upstreamCertificate
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import Data.Bits (testBit)
import qualified Data.List as L

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.Word as Word
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Simplicity, Primitive)
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Jets (unwrap)
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.Kernels (nibble8)
import qualified JetDiscovery.Lib.ShrincsHash as ShrincsHash
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.SlhDsaStandard as Ref
import JetDiscovery.Lib.TxSer (ctxWith)

pick :: (Core term, TyC x, TyC c) => Bool -> term x c -> term (x, x) c
pick True = drop
pick False = take

nibble :: Core term => Int -> term Word128 Word4
nibble k = pick (testBit k 4) (pick (testBit k 3) (pick (testBit k 2) (pick (testBit k 1) (pick (testBit k 0) iden))))

bit64 :: Core term => Int -> term Word64 Bit
bit64 k = pick (testBit p 5) (pick (testBit p 4) (pick (testBit p 3) (pick (testBit p 2) (pick (testBit p 1) (pick (testBit p 0) iden))))) where p = 63 - k

low32 :: Core term => term Word64 Word32
low32 = ih

w128FromBytes :: BS.ByteString -> Word128
w128FromBytes = toWord128 . BS.foldl' (\a b -> a * 256 + toInteger b) 0

-- | Append f(s) to the context while keeping s.
add :: (Core term, TyC s, TyC x) => term s x -> term (Ctx8, x) Ctx8 -> term (Ctx8, s) (Ctx8, s)
add f jet = ((oh &&& drop f) >>> jet) &&& ih

-- | Start from a context computed without input, thread the additions, finalize and truncate to 16 bytes.
hash16 :: (Assert term, TyC s) => term s Ctx8 -> term (Ctx8, s) (Ctx8, s) -> term s Word128
hash16 start steps = (start &&& iden) >>> steps >>> oh >>> ctx8Finalize >>> oh

kw8 :: (Core term, TyC s) => Integer -> term s Word8
kw8 = konst . w8
kw32 :: (Core term, TyC s) => Integer -> term s Word32
kw32 = konst . w32
kw64 :: (Core term, TyC s) => Integer -> term s Word64
kw64 = konst . w64

shr :: Core term => Int -> term Word64 Word64
shr n = (konst (w8 (toInteger n)) &&& iden) >>> Word.right_shift word8 word64

-- | Order (node, sibling) by bit k of an index.
ordered :: (Core term, TyC s) => term s Bit -> term s Word128 -> term s Word128 -> term s Word256
ordered b node sib = (b &&& (node &&& sib)) >>> cond (ih &&& oh) iden

data SW = SW
  { swPk :: (Word128, Word128)                    -- ^ (PK.seed, PK.root)
  , swR :: Word128
  , swFors :: [(Word128, [Word128])]               -- ^ 14 x (preimage, 12 auth)
  , swLayers :: [([Word128], [Word128])]           -- ^ 7 x (35 chains, 9 auth)
  }

type SSHeader=(Word128,(Word128,Word128))
type SSInput=SSHeader
type I0=(SSInput,(Word256,(Word64,Word64)))
type LS=(SSInput,(Word128,(Word64,Word64)))

packSS :: SW -> SSInput
packSS sw
 | length (swFors sw)/=14 || any ((/=12).length.snd) (swFors sw) || length (swLayers sw)/=7 || any (\(c,a)->length c/=35||length a/=9) (swLayers sw)=error "SLHDSA standard proof dimensions"
 | otherwise=(pkSeed,(slRoot,swR sw))
 where (pkSeed,slRoot)=swPk sw

pkSeedT :: Core term => term SSInput Word128
pkSeedT=oh
slRootT :: Core term => term SSInput Word128
slRootT=ih >>> oh
randomizerT :: Core term => term SSInput Word128
randomizerT=ih >>> ih
seedMid :: Assert term => term Word128 Ctx8
seedMid=((unit >>> ctx8Init) &&& ((iden &&& konst (toWord128 0)) &&& konst (toWord256 0))) >>> ctx8Add64

-- The pure shared kernel accepts a seeded compression state and the exact
--18-byte address prefix. This wrapper supplies the stateless type0 address.
type DirectWotsInput=((Word128,(Word8,Word64)),((Word32,Word32),(Word4,Word128)))
directWotsChain :: forall term. Simplicity term => term DirectWotsInput Word128
directWotsChain=((ooh >>> ShrincsHash.seedState) &&& ((oih &&& (kw8 0 &&& ioh)) &&& iih)) >>> ShrincsHash.chain

appendT :: (Assert term,TyC a,TyC b) => term a b -> term (Ctx8,b) Ctx8 -> term (a,Ctx8) (a,Ctx8)
appendT f jet=oh &&& ((ih &&& (oh >>> f)) >>> jet)
startHash :: (Assert term,TyC a) => term a (a,Ctx8)
startHash=iden &&& (unit >>> ctx8Init)
endHash :: (Assert term,TyC a) => term (a,Ctx8) Word256
endHash=drop ctx8Finalize

-- Bind the multiply-used header once and retain it as data. Each independent
-- proof word enters once at its consuming stage; checked/derived values never
-- return through witness. This keeps the carried state small and binding sound.
slhDsa :: forall term. (Simplicity term,Primitive term) => SW -> term () ()
slhDsa=slhDsaWith (ctxWith (konst (w16 0)) ctx8Add2 >>> ctxWith (unwrap (Jets.jetSubst SigHash.sigAllHash)) ctx8Add32)
slhDsaWith :: forall term. (Simplicity term,Primitive term) => term Ctx8 Ctx8 -> SW -> term () ()
slhDsaWith appendMessage sw=witness (packSS sw) >>> statelessT appendMessage sw
statelessT :: forall term. (Simplicity term,Primitive term) => term Ctx8 Ctx8 -> SW -> term SSInput ()
statelessT appendMessage sw=(computedRoot &&& slRootT) >>> eq >>> verify
 where
  -- All490independent proof words enter once:14*(1+12) FORS fields,
  --then7*(35chain+9path). The public key/randomizer header is bound once.
  proofWords=concat [p:a|(p,a)<-swFors sw]++concat [c++a|(c,a)<-swLayers sw]
  proofAt :: forall a. TyC a => Int -> term a Word128
  proofAt i | i>=0 && i<490=witness (proofWords!!i)
            | otherwise=error "SLHDSA standard proof index"
  inner=startHash >>> appendT randomizerT ctx8Add16 >>> appendT pkSeedT ctx8Add16 >>> appendT slRootT ctx8Add16
        >>> (oh &&& drop appendMessage) >>> endHash
  digest=startHash >>> appendT randomizerT ctx8Add16 >>> appendT pkSeedT ctx8Add16 >>> appendT inner ctx8Add32
         >>> appendT (konst (w32 0)) ctx8Add4 >>> endHash
  field :: Int -> Integer -> term Word256 Word64
  field s w=(Word.shift_const_by false word256 (negate s) >>> drop ih) &&& kw64 (2^w-1) >>> Word.bitwise_and word64
  treeIdx=field 32 54
  leafIdx=field 16 9
  input0=(iden &&& digest) >>> (oh &&& (ih &&& ((ih >>> treeIdx) &&& (ih >>> leafIdx))))
  computedRoot=input0 >>> (oh &&& (forsPk &&& (ih >>> ih))) >>> hypertree >>> ih >>> oh
  -- FORS: bound input + digest/tree/leaf remain together at each stage.
  forsPk :: term I0 Word128
  forsPk=(iden &&& roots) >>> hash16 (take (oh >>> pkSeedT >>> seedMid))
          (add (kw8 0) ctx8Add1 >>> add (take (ih >>> ioh)) ctx8Add8 >>> add (kw8 4) ctx8Add1 >>> add (take (ih >>> iih >>> low32)) ctx8Add4
           >>> add (kw64 0) ctx8Add8 >>> add (drop oh) ctx8Add128 >>> add (drop ioh) ctx8Add64 >>> add (drop iih) ctx8Add32)
   where
    roots=rootTree [forsTree i|i<-[0..13]]
    rootTree [a,b,c,d,e,f,g,h,i,j,k,l,m,n]=(((a&&&b)&&&(c&&&d))&&&((e&&&f)&&&(g&&&h)))&&&(((i&&&j)&&&(k&&&l))&&&(m&&&n))
    rootTree _=error "FORS roots"
  forsTree :: Int -> term I0 Word128
  forsTree i=(iden &&& ti) >>> (leaf &&& iden) >>> L.foldl' (>>>) iden [level j &&& ih|j<-[0..11]] >>> oh
   where
    ti=((ih >>> oh >>> field (256-12*(i+1)) 12) &&& kw64 (toInteger i*4096)) >>> Arith.add word64 >>> ih
    common=add (kw8 0) ctx8Add1 >>> add (take (ih >>> ioh)) ctx8Add8 >>> add (kw8 3) ctx8Add1 >>> add (take (ih >>> iih >>> low32)) ctx8Add4
    leaf=hash16 (take (oh >>> pkSeedT >>> seedMid)) (common >>> add (kw32 0) ctx8Add4 >>> add (ih >>> low32) ctx8Add4 >>> add (take (oh >>> proofAt (13*i))) ctx8Add16)
    level j=hash16 (drop (take (oh >>> pkSeedT >>> seedMid)))
      (add (kw8 0) ctx8Add1 >>> add (drop (take (ih >>> ioh))) ctx8Add8 >>> add (kw8 3) ctx8Add1
       >>> add (drop (take (ih >>> iih >>> low32))) ctx8Add4 >>> add (kw32 (toInteger j+1)) ctx8Add4
       >>> add (drop (ih >>> shr (j+1) >>> low32)) ctx8Add4
       >>> add (ordered (drop (ih >>> bit64 j)) oh (drop (take (oh >>> proofAt (13*i+1+j))))) ctx8Add32)
  -- Hypertree: all layers consume the same bound proof, with message/tree/leaf
  -- values passed through unary stages rather than reconstructed by witness.
  hypertree :: term LS LS
  hypertree=L.foldl' (>>>) iden [layer j|j<-[0..6]]
  layer :: Int -> term LS LS
  layer j=(((iden &&& checksum) >>> wotsPk) &&& iden)
          >>> L.foldl' (>>>) iden [xmssLevel k &&& ih|k<-[0..8]]
          >>> (drop oh &&& (oh &&& ((drop (ih >>> ioh >>> shr 9)) &&& ((drop (ih >>> ioh) &&& kw64 511) >>> Word.bitwise_and word64))))
   where
    lj=toInteger j
    base=182+44*j
    checksum :: term LS Word16
    checksum=(kw16 480 &&& L.foldl' (\acc k -> (acc &&& (ih >>> oh >>> nibble k >>> nibble8 >>> (kw8 0 &&& iden))) >>> Arith.add word16 >>> ih) (kw16 0) [0..31]) >>> Arith.subtract word16 >>> ih
    kw16 :: TyC a => Integer -> term a Word16
    kw16=konst.w16
    start :: Int -> term (LS,Word16) Word4
    start i | i<32=take (ih >>> oh >>> nibble i)
            | i==32=drop (take ih)
            | i==33=drop (drop oh)
            | otherwise=drop (drop ih)
    chain :: Int -> term (LS,Word16) Word128
    chain i=(((take (oh >>> pkSeedT) &&& (kw8 lj &&& take (ih >>> ioh))) &&&
              ((take (ih >>> iih >>> low32) &&& kw32 (toInteger i)) &&&
               (start i &&& take (oh >>> proofAt (base+i)))))) >>> directWotsChain
    tips :: term (LS,Word16) (Word4096,(Word256,Word128))
    tips=tree32 [chain i|i<-[0..31]] &&& ((chain 32 &&& chain 33) &&& chain 34)
    wotsPk :: term (LS,Word16) Word128
    wotsPk=(iden &&& tips) >>> hash16 (take (take (oh >>> pkSeedT >>> seedMid)))
      (add (kw8 lj) ctx8Add1 >>> add (take (take (ih >>> ioh))) ctx8Add8 >>> add (kw8 1) ctx8Add1 >>> add (take (take (ih >>> iih >>> low32))) ctx8Add4
       >>> add (kw64 0) ctx8Add8 >>> add (drop oh) ctx8Add512 >>> add (drop ioh) ctx8Add32 >>> add (drop iih) ctx8Add16)
    xmssLevel :: Int -> term (Word128,LS) Word128
    xmssLevel k=hash16 (drop (oh >>> pkSeedT >>> seedMid))
      (add (kw8 lj) ctx8Add1 >>> add (drop (ih >>> ioh)) ctx8Add8 >>> add (kw8 2) ctx8Add1 >>> add (kw32 0) ctx8Add4
       >>> add (kw32 (toInteger k+1)) ctx8Add4 >>> add (drop (ih >>> iih >>> shr (k+1) >>> low32)) ctx8Add4
       >>> add (ordered (drop (ih >>> iih >>> bit64 k)) oh (drop (oh >>> proofAt (base+35+k)))) ctx8Add32)

tree32 :: (Core term, TyC a) => [term a Word128] -> term a Word4096
tree32 ts = p16 (L.take 16 ts) &&& p16 (L.drop 16 ts)
 where
  p16 xs = p8 (L.take 8 xs) &&& p8 (L.drop 8 xs)
  p8 xs = p4 (L.take 4 xs) &&& p4 (L.drop 4 xs)
  p4 xs = p2 (L.take 2 xs) &&& p2 (L.drop 2 xs)
  p2 [a, b] = a &&& b
  p2 _ = error "tree32"

-- Derived transaction vectors; official ACVP fixtures are loaded separately.
entries :: [Entry]
entries=[Entry
 {entryId="pq-slh-dsa-sha2-128s"
 ,entryTitle="FIPS205 SLH-DSA-SHA2-128s full transaction signature verifier"
 ,entrySpec="FIPS205 algorithms3,6,9,12,14,15,20,24 and11.2.1; vendor-specs/slhdsa/fips205.pdf"
 ,entryCategory=PostQuantum
 ,entryVectorSource=Derived "independent ByteString verifier and fixed-secret verification fixture generator in Ref.SlhDsaStandard; official ACVP fixtures separately"
 ,entryAssumptions=["standard n16,h63,d7,hprime9,k14,a12,w16, publickey32bytes, signature7856bytes", "pure external API, empty context, message=sig_all_hash; no prehash or other parameter sets counted", "typed witness maps fixed public-key/signature fields; each proof word enters once", "standard baseline belongs to the same hash-family parameter counting group, not a new distinct application"]
 ,entryProgram = \sw->Prog (slhDsa sw)
 ,entryVectors=[Vector "valid standard signature (reference accepts)" env swValid Accept
   ,Vector "corrupted FORS preimage" env (swValid{swFors=(toWord128 0,snd(head(swFors swValid))):L.drop 1(swFors swValid)}) Reject
   ,Vector "corrupted top-layer chain" env (swValid{swLayers=L.take 6(swLayers swValid)++[(toWord128 1:L.drop 1(fst(last(swLayers swValid))),snd(last(swLayers swValid)))]}) Reject
   ,Vector "same-CMR seed splice" env (swValid{swPk=(toWord128 0,snd(swPk swValid))}) Reject
   ,Vector "same-CMR randomizer splice" env (swValid{swR=toWord128 0}) Reject
   ,Vector "same-CMR claimed-root splice" env (swValid{swPk=(fst(swPk swValid),toWord128 0)}) Reject
   ,Vector "different transaction" env2 swValid Reject]}]
 where
  env=mkEnv (mkTx 2 [mkInput(dummyOutpoint 0)100000 mempty 0xffffffff][mkOutput 99000(unhex "0014"<>BS.replicate 20 1)]0)0 defaultTap
  env2=mkEnv (mkTx 2 [mkInput(dummyOutpoint 0)100000 mempty 0xffffffff][mkOutput 98000(unhex "0014"<>BS.replicate 20 1)]0)0 defaultTap
  pkSeed=BS.replicate 16 0x5e;sk=BS.replicate 16 0x9f
  dummy=SW (toWord128 0,toWord128 0)(toWord128 0)(replicate 14(toWord128 0,replicate 12(toWord128 0)))(replicate 7(replicate 35(toWord128 0),replicate 9(toWord128 0)))
  cmr=progCmr (Prog(slhDsa dummy))
  msgOf=maybe(error "SLHDSA environment")(\e->maybe(error "SLHDSA sighash")w256ToBytes(Jets.fastEval(unwrap(Jets.jetSubst SigHash.sigAllHash))e()))(env cmr)
  (publicRoot,signature)=Ref.signStateless sk pkSeed msgOf
  swValid | Ref.verifyStateless pkSeed publicRoot msgOf signature=SW (w128FromBytes pkSeed,w128FromBytes publicRoot)(w128FromBytes(Ref.slR signature))
     [(w128FromBytes p,map w128FromBytes a)|(p,a)<-Ref.slFors signature]
     [(map w128FromBytes c,map w128FromBytes a)|(c,a)<-Ref.slLayers signature]
          | otherwise=error "independent standard SLHDSA reference rejected fixture"

-- Non-counted interoperability fixture: official ACVP pure case266. M' already
-- contains its0x00/255-byte-context prefix; hash it in full inside Simplicity.
upstreamCertificate :: IO Entry
upstreamCertificate=do
 raw<-readFile "vendor-specs/slhdsa/acvp-selected-kat.txt"
 let rows=[(k,L.drop 1 v)|line<-lines raw,(k,v)<-[break(=='=')line]]
     field k=maybe(error("ACVP missing "++k))unhex(lookup k rows)
     publickey=field "publickey";message=field "framedmessage";sigBytes=field "signature"
     signature=maybe(error "ACVP signature format")id(Ref.parseSignature sigBytes)
     seed=BS.take 16 publickey;root=BS.drop 16 publickey
     referenceOk=BS.length publickey==32 && Ref.verifyInternal seed root message signature
     good=SW (w128FromBytes seed,w128FromBytes root)(w128FromBytes(Ref.slR signature))
          [(w128FromBytes p,map w128FromBytes a)|(p,a)<-Ref.slFors signature]
          [(map w128FromBytes c,map w128FromBytes a)|(c,a)<-Ref.slLayers signature]
     chunks bytes | BS.null bytes=[]
                  | otherwise=BS.take 511 bytes:chunks(BS.drop 511 bytes)
     appendMessage :: forall term. Assert term => term Ctx8 Ctx8
     appendMessage=foldl(>>>)iden[ctxWith(konst(buffer511FromBytes chunk))ctx8AddBuffer511|chunk<-chunks message]
     program w=Prog(slhDsaWith appendMessage w)
     env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)100000 mempty 0xffffffff][mkOutput 99000 mempty]0)0 defaultTap
     badChain=good{swFors=(toWord128 0,snd(head(swFors good))):L.drop 1(swFors good)}
 if referenceOk == False then error "ACVP official positive rejected by independent reference" else pure Entry
  {entryId="test-fips205-acvp-sha2-128s-case266"
  ,entryTitle="Official NIST ACVP FIPS205 SHA2-128s pure signature (max255-byte context)"
  ,entrySpec="ACVP-Server@975de31e group19/case266, external pure FIPS205"
  ,entryCategory=PostQuantum
  ,entryVectorSource=Upstream "vendor-specs/slhdsa/acvp-selected-kat.txt extracted from full42case parameter subset"
  ,entryAssumptions=["non-counted fixture; exact281-byte framed message hashed inside Simplicity", "all28pure/internal official cases are separately checked by independent reference;14preHash cases are outside this pure baseline"]
  ,entryProgram=program
  ,entryVectors=[Vector "official ACVP case266" env good Accept
    ,Vector "same-CMR corrupted FORS preimage" env badChain Reject
    ,Vector "same-CMR changed public seed" env (good{swPk=(toWord128 0,snd(swPk good))}) Reject
    ,Vector "same-CMR changed randomizer" env (good{swR=toWord128 0}) Reject]}
