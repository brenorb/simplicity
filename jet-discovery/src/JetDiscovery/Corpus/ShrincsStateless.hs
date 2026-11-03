{-# LANGUAGE ScopedTypeVariables #-}
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
  ( entries
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
import JetDiscovery.Lib.Kernels (wotsChain, nibble8)
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
hash16 :: (Assert term, TyC s) => term () Ctx8 -> term (Ctx8, s) (Ctx8, s) -> term s Word128
hash16 start steps = ((unit >>> start) &&& iden) >>> steps >>> oh >>> ctx8Finalize >>> oh

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

type I0 = (Word256, (Word64, Word64))    -- (digest, (tree index, leaf index))
type LS = (Word128, (Word64, Word64))     -- (message, (tree, leaf)) for a hypertree layer

shrincsStateless :: forall term. (Simplicity term, Primitive term) => SW -> term () ()
shrincsStateless sw = (digest >>> (iden &&& (treeIdx &&& leafIdx)) >>> (forsPk &&& ih) >>> hypertree >>> oh) &&& slRootT >>> eq >>> verify
 where
  (pkSeedV, (slRootV, sfRootV)) = swPk sw
  pkSeedT, slRootT, sfRootT :: forall a. TyC a => term a Word128
  pkSeedT = witness pkSeedV
  slRootT = witness slRootV
  sfRootT = witness sfRootV
  mid :: term () Ctx8
  mid = ctx8Init &&& ((pkSeedT &&& konst (toWord128 0)) &&& konst (toWord256 0)) >>> ctx8Add64
  ctxW :: TyC x => term () x -> term (Ctx8, x) Ctx8 -> term Ctx8 Ctx8
  ctxW t jet = iden &&& (unit >>> t) >>> jet
  -- H_msg_sl(R, pk_seed, sl_root, 0x00 0x00 || sf_root || sig_all_hash)
  msg = unwrap (Jets.jetSubst SigHash.sigAllHash)
  inner = ctx8Init >>> ctxW (witness (swR sw)) ctx8Add16 >>> ctxW pkSeedT ctx8Add16 >>> ctxW slRootT ctx8Add16
      >>> ctxW (konst (w16 0)) ctx8Add2 >>> ctxW sfRootT ctx8Add16 >>> ctxW msg ctx8Add32 >>> ctx8Finalize
  digest :: term () Word256
  digest = ctx8Init >>> ctxW (witness (swR sw)) ctx8Add16 >>> ctxW pkSeedT ctx8Add16 >>> ctxW inner ctx8Add32
       >>> ctxW (konst (w32 0)) ctx8Add4 >>> ctx8Finalize
  -- bits [256 - s - w, 256 - s) of the digest as a 64-bit word
  field :: Int -> Integer -> term Word256 Word64
  field s w = (Word.shift_const_by false word256 (negate s) >>> drop ih) &&& kw64 (2 ^ w - 1) >>> Word.bitwise_and word64
  treeIdx = field (256 - 176) 36
  leafIdx = field (256 - 192) 9
  -- FORS ------------------------------------------------------------------------------
  forsPk :: term I0 Word128
  forsPk = (iden &&& roots) >>> hash16 mid
             (add (kw8 0) ctx8Add1 >>> add (take ioh) ctx8Add8 >>> add (kw8 4) ctx8Add1 >>> add (take (iih >>> low32)) ctx8Add4
              >>> add (kw64 0) ctx8Add8 >>> add (drop oh) ctx8Add128 >>> add (drop ih) ctx8Add32)
   where
    roots = rootTree [ forsTree i (swFors sw !! i) | i <- [0 .. 9] ]
    rootTree [a, b, c, d, e, f, g, h, i, j] = (((a &&& b) &&& (c &&& d)) &&& ((e &&& f) &&& (g &&& h))) &&& (i &&& j)
    rootTree _ = error "fors roots"
  -- one FORS tree: input I0; state (node, (I0, tree index of the leaf))
  forsTree :: Int -> (Word128, [Word128]) -> term I0 Word128
  forsTree i (pre, auth) = (iden &&& ti) >>> (leaf &&& iden) >>> L.foldl' (\acc (j, sib) -> acc >>> (level j sib &&& ih)) iden (zip [0 ..] auth) >>> oh
   where
    ti = (field (256 - 13 * (i + 1)) 13 `onDigest` ()) &&& kw64 (toInteger i * 8192) >>> Arith.add word64 >>> ih
    onDigest f () = take f
    common = add (kw8 0) ctx8Add1 >>> add (take ioh) ctx8Add8 >>> add (kw8 3) ctx8Add1 >>> add (take (iih >>> low32)) ctx8Add4
    -- leaf: F(ForsTree(0, tree, leaf, 0, ti), preimage); input (I0, ti)
    leaf = hash16 mid (common >>> add (kw32 0) ctx8Add4 >>> add (ih >>> low32) ctx8Add4 >>> add (unit >>> witness pre) ctx8Add16)
    -- level j: H(ForsTree(0, tree, leaf, j + 1, ti >> (j + 1)), ordered pair); input (node, (I0, ti))
    level j sib = hash16 mid (add (drop (take ioh)) ctx8Add8 `after` add (kw8 0) ctx8Add1
                    >>> add (kw8 3) ctx8Add1 >>> add (drop (take (iih >>> low32))) ctx8Add4 >>> add (kw32 (toInteger j + 1)) ctx8Add4
                    >>> add (drop (ih >>> shr (j + 1) >>> low32)) ctx8Add4
                    >>> add (ordered (drop (ih >>> bit64 j)) oh (unit >>> witness sib)) ctx8Add32)
    after b a = a >>> b
  -- Hypertree -------------------------------------------------------------------------
  hypertree :: term LS LS
  hypertree = L.foldl' (\acc (j, l) -> acc >>> layer j l) iden (zip [0 ..] (swLayers sw))
  layer :: Int -> ([Word128], [Word128]) -> term LS LS
  layer j (chains, auth) = (((iden &&& checksum) >>> wotsPk) &&& iden)
                       >>> L.foldl' (\acc (k, sib) -> acc >>> (xmssLevel k sib &&& ih)) iden (zip [0 ..] auth)
                       >>> (oh &&& ((drop (ioh >>> shr 9)) &&& (drop ioh &&& kw64 511 >>> Word.bitwise_and word64)))
   where
    lj = toInteger j
    -- checksum = 480 - sum of the 32 message nibbles; input S
    checksum :: term LS Word16
    checksum = kw16 480 &&& L.foldl' (\acc k -> (acc &&& (oh >>> nibble k >>> nibble8 >>> (kw8 0 &&& iden))) >>> Arith.add word16 >>> ih) (kw16 0) [0 .. 31]
               >>> Arith.subtract word16 >>> ih
    kw16 :: TyC s => Integer -> term s Word16
    kw16 = konst . w16
    -- start index of chain i; input (S, checksum)
    start :: Int -> term (LS, Word16) Word4
    start i | i < 32 = take (oh >>> nibble i)
            | i == 32 = drop (take ih)
            | i == 33 = drop (drop oh)
            | otherwise = drop (drop ih)
    chain :: Int -> Word128 -> term (LS, Word16) Word128
    chain i c = (pre &&& (start i &&& (unit >>> witness c))) >>> wotsChain
     where pre = ((unit >>> mid) &&& iden) >>> (add (kw8 lj) ctx8Add1 >>> add (take ioh) ctx8Add8 >>> add (kw8 0) ctx8Add1
                   >>> add (take (iih >>> low32)) ctx8Add4 >>> add (kw32 (toInteger i)) ctx8Add4) >>> oh
    tips :: term (LS, Word16) (Word4096, (Word256, Word128))
    tips = tree32 [ chain i c | (i, c) <- zip [0 .. 31] chains ] &&& ((chain 32 (chains !! 32) &&& chain 33 (chains !! 33)) &&& chain 34 (chains !! 34))
    -- T_sl(WotsTwPk(j, tree, leaf), tips); input (S, checksum)
    wotsPk :: term (LS, Word16) Word128
    wotsPk = (iden &&& tips) >>> hash16 mid
               (add (kw8 lj) ctx8Add1 >>> add (take (take ioh)) ctx8Add8 >>> add (kw8 1) ctx8Add1 >>> add (take (take (iih >>> low32))) ctx8Add4
                >>> add (kw64 0) ctx8Add8 >>> add (drop oh) ctx8Add512 >>> add (drop ioh) ctx8Add32 >>> add (drop iih) ctx8Add16)
    -- XMSS level k: H(XmssTree(j, tree, k + 1, leaf >> (k + 1)), ordered pair); state (node, S)
    xmssLevel :: Int -> Word128 -> term (Word128, LS) Word128
    xmssLevel k sib = hash16 mid
      (add (kw8 lj) ctx8Add1 >>> add (drop ioh) ctx8Add8 >>> add (kw8 2) ctx8Add1 >>> add (kw32 0) ctx8Add4
       >>> add (kw32 (toInteger k + 1)) ctx8Add4 >>> add (drop (iih >>> shr (k + 1) >>> low32)) ctx8Add4
       >>> add (ordered (drop (iih >>> bit64 k)) oh (unit >>> witness sib)) ctx8Add32)

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
