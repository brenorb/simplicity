{-# LANGUAGE ScopedTypeVariables, GADTs #-}
-- | SHRINCS stateless signature verification (the SLH-DSA path of
-- vendor-specs/shrincs/SHRINCS.md: FORS with k = 10, a = 13, then a 5-layer
-- hypertree of WOTS-TW + XMSS with h' = 9), on sig_all_hash with an empty
-- context.  Up to 2,792 SHA-256 compressions per the spec.
--
-- Every WOTS-TW chain uses the same kernel as the stateful path
-- ("JetDiscovery.Lib.Kernels".wotsChain): the 22-byte address layouts agree up
-- to the chain index.  Values used more than once (digest, tree and leaf
-- indices, checksum, chain tips) are computed once and carried as data.
module JetDiscovery.Corpus.ShrincsStateless
  ( entries, directWotsChain
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
import qualified JetDiscovery.Ref.SlhDsa as Ref

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
  { swPk :: (Word128, (Word128, Word128))          -- ^ (pk_seed, sl_root, sf_root)
  , swR :: Word128
  , swFors :: [(Word128, [Word128])]               -- ^ 10 x (preimage, 13 auth)
  , swLayers :: [([Word128], [Word128])]           -- ^ 5 x (35 chains, 9 auth)
  }

type SSHeader=(Word128,(Word128,(Word128,Word128)))
type SSInput=SSHeader
type I0=(SSInput,(Word256,(Word64,Word64)))
type LS=(SSInput,(Word128,(Word64,Word64)))

packSS :: SW -> SSInput
packSS sw
 | length (swFors sw)/=10 || any ((/=13).length.snd) (swFors sw) || length (swLayers sw)/=5 || any (\(c,a)->length c/=35||length a/=9) (swLayers sw)=error "SHRINCS stateless proof dimensions"
 | otherwise=(pkSeed,(slRoot,(sfRoot,swR sw)))
 where (pkSeed,(slRoot,sfRoot))=swPk sw

pkSeedT :: Core term => term SSInput Word128
pkSeedT=oh
slRootT :: Core term => term SSInput Word128
slRootT=ih >>> oh
sfRootT :: Core term => term SSInput Word128
sfRootT=ih >>> ih >>> oh
randomizerT :: Core term => term SSInput Word128
randomizerT=ih >>> ih >>> ih
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
shrincsStateless :: forall term. (Simplicity term,Primitive term) => SW -> term () ()
shrincsStateless sw=witness (packSS sw) >>> statelessT sw
statelessT :: forall term. (Simplicity term,Primitive term) => SW -> term SSInput ()
statelessT sw=(computedRoot &&& slRootT) >>> eq >>> verify
 where
  -- All360independent proof words are consumed at exactly one stage each:
  --140FORS fields, then5*(35chain+9path). Header values are pure projections.
  proofWords=concat [p:a|(p,a)<-swFors sw]++concat [c++a|(c,a)<-swLayers sw]
  proofAt :: forall a. TyC a => Int -> term a Word128
  proofAt i | i>=0 && i<360=witness (proofWords!!i)
            | otherwise=error "SHRINCS stateless proof index"
  msg=unit >>> unwrap (Jets.jetSubst SigHash.sigAllHash)
  inner=startHash >>> appendT randomizerT ctx8Add16 >>> appendT pkSeedT ctx8Add16 >>> appendT slRootT ctx8Add16
        >>> appendT (konst (w16 0)) ctx8Add2 >>> appendT sfRootT ctx8Add16 >>> appendT msg ctx8Add32 >>> endHash
  digest=startHash >>> appendT randomizerT ctx8Add16 >>> appendT pkSeedT ctx8Add16 >>> appendT inner ctx8Add32
         >>> appendT (konst (w32 0)) ctx8Add4 >>> endHash
  field :: Int -> Integer -> term Word256 Word64
  field s w=(Word.shift_const_by false word256 (negate s) >>> drop ih) &&& kw64 (2^w-1) >>> Word.bitwise_and word64
  treeIdx=field (256-176) 36
  leafIdx=field (256-192) 9
  input0=(iden &&& digest) >>> (oh &&& (ih &&& ((ih >>> treeIdx) &&& (ih >>> leafIdx))))
  computedRoot=input0 >>> (oh &&& (forsPk &&& (ih >>> ih))) >>> hypertree >>> ih >>> oh
  -- FORS: bound input + digest/tree/leaf remain together at each stage.
  forsPk :: term I0 Word128
  forsPk=(iden &&& roots) >>> hash16 (take (oh >>> pkSeedT >>> seedMid))
          (add (kw8 0) ctx8Add1 >>> add (take (ih >>> ioh)) ctx8Add8 >>> add (kw8 4) ctx8Add1 >>> add (take (ih >>> iih >>> low32)) ctx8Add4
           >>> add (kw64 0) ctx8Add8 >>> add (drop oh) ctx8Add128 >>> add (drop ih) ctx8Add32)
   where
    roots=rootTree [forsTree i|i<-[0..9]]
    rootTree [a,b,c,d,e,f,g,h,i,j]=(((a&&&b)&&&(c&&&d))&&&((e&&&f)&&&(g&&&h)))&&&(i&&&j)
    rootTree _=error "FORS roots"
  forsTree :: Int -> term I0 Word128
  forsTree i=(iden &&& ti) >>> (leaf &&& iden) >>> L.foldl' (>>>) iden [level j &&& ih|j<-[0..12]] >>> oh
   where
    ti=((ih >>> oh >>> field (256-13*(i+1)) 13) &&& kw64 (toInteger i*8192)) >>> Arith.add word64 >>> ih
    common=add (kw8 0) ctx8Add1 >>> add (take (ih >>> ioh)) ctx8Add8 >>> add (kw8 3) ctx8Add1 >>> add (take (ih >>> iih >>> low32)) ctx8Add4
    leaf=hash16 (take (oh >>> pkSeedT >>> seedMid)) (common >>> add (kw32 0) ctx8Add4 >>> add (ih >>> low32) ctx8Add4 >>> add (take (oh >>> proofAt (14*i))) ctx8Add16)
    level j=hash16 (drop (take (oh >>> pkSeedT >>> seedMid)))
      (add (kw8 0) ctx8Add1 >>> add (drop (take (ih >>> ioh))) ctx8Add8 >>> add (kw8 3) ctx8Add1
       >>> add (drop (take (ih >>> iih >>> low32))) ctx8Add4 >>> add (kw32 (toInteger j+1)) ctx8Add4
       >>> add (drop (ih >>> shr (j+1) >>> low32)) ctx8Add4
       >>> add (ordered (drop (ih >>> bit64 j)) oh (drop (take (oh >>> proofAt (14*i+1+j))))) ctx8Add32)
  -- Hypertree: all layers consume the same bound proof, with message/tree/leaf
  -- values passed through unary stages rather than reconstructed by witness.
  hypertree :: term LS LS
  hypertree=L.foldl' (>>>) iden [layer j|j<-[0..4]]
  layer :: Int -> term LS LS
  layer j=(((iden &&& checksum) >>> wotsPk) &&& iden)
          >>> L.foldl' (>>>) iden [xmssLevel k &&& ih|k<-[0..8]]
          >>> (drop oh &&& (oh &&& ((drop (ih >>> ioh >>> shr 9)) &&& ((drop (ih >>> ioh) &&& kw64 511) >>> Word.bitwise_and word64))))
   where
    lj=toInteger j
    base=140+44*j
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

-- Vectors ------------------------------------------------------------------------

entries :: [Entry]
entries =
  [ Entry
    { entryId = "pq-shrincs-stateless"
    , entryTitle = "SHRINCS stateless signature (SLH-DSA path: FORS + 5-layer hypertree) on sig_all_hash"
    , entrySpec = "SHRINCS draft (vendor-specs/shrincs/SHRINCS.md), slh_dsa_verify with SHRINCS parameters"
    , entryCategory = PostQuantum
    , entryVectorSource = Derived "signatures from JetDiscovery.Ref.SlhDsa (top XMSS tree computed in full; the reference verifier also accepts each positive vector)"
    , entryAssumptions = ["message = sig_all_hash, empty context; the 48-byte public key is a witness operand"]
    , entryProgram = \w -> Prog (shrincsStateless w)
    , entryVectors =
        [ Vector ("valid stateless signature" ++ refNote) env swValid Accept
        , Vector "corrupted FORS preimage" env (swValid { swFors = (toWord128 0, snd (head (swFors swValid))) : L.drop 1 (swFors swValid) }) Reject
        , Vector "corrupted top-layer chain" env (swValid { swLayers = L.take 4 (swLayers swValid) ++ [ (toWord128 1 : L.drop 1 (fst (last (swLayers swValid))), snd (last (swLayers swValid))) ] }) Reject
        , Vector "same-CMR seed/header splice" env (swValid {swPk=(toWord128 0,(fst (snd (swPk swValid)),snd (snd (swPk swValid))))}) Reject
        , Vector "same-CMR randomizer splice" env (swValid {swR=toWord128 0}) Reject
        , Vector "same-CMR claimed root splice" env (swValid {swPk=(fst (swPk swValid),(toWord128 0,snd (snd (swPk swValid))))}) Reject
        , Vector "signature for another transaction" env2 swValid Reject ]
    }
  ]
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xffffffff] [mkOutput 99000 (unhex "0014" <> BS.replicate 20 1)] 0) 0 defaultTap
  env2 = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xffffffff] [mkOutput 98000 (unhex "0014" <> BS.replicate 20 1)] 0) 0 defaultTap
  pkSeed = BS.replicate 16 0x5e
  sk = BS.replicate 16 0x9f
  sfRoot = BS.replicate 16 0x33
  dummy = SW (toWord128 0, (toWord128 0, toWord128 0)) (toWord128 0) (replicate 10 (toWord128 0, replicate 13 (toWord128 0))) (replicate 5 (replicate 35 (toWord128 0), replicate 9 (toWord128 0)))
  cmr = progCmr (Prog (shrincsStateless dummy))
  msgOf = maybe (error "env") (\e -> maybe (error "sighash") w256ToBytes (Jets.fastEval (unwrap (Jets.jetSubst SigHash.sigAllHash)) e ())) (env cmr)
  bound = sfRoot <> msgOf
  (slRoot, sig) = Ref.signStateless sk pkSeed bound
  refNote = if Ref.verifyStateless pkSeed slRoot bound sig then "" else " (REFERENCE REJECTS)"
  swValid = SW (w128FromBytes pkSeed, (w128FromBytes slRoot, w128FromBytes sfRoot)) (w128FromBytes (Ref.slR sig))
               [ (w128FromBytes p, map w128FromBytes a) | (p, a) <- Ref.slFors sig ]
               [ (map w128FromBytes c, map w128FromBytes a) | (c, a) <- Ref.slLayers sig ]
