{-# LANGUAGE ScopedTypeVariables #-}
-- | SHRINCS stateful signature verification (draft SHRINCS spec,
-- vendor-specs/shrincs/SHRINCS.md), with the message set to sig_all_hash
-- and an empty context, as a Bitcoin spend would use it.
--
-- The verifier recomputes a WOTS+C public key (32 chains of up to 15 F calls,
-- one T_sf over 512 bytes), then walks an FXMSS authentication path of up to
-- 'maxDepth' H calls.  Every tweakable hash is SHA-256 over a cached
-- @pk_seed || zeros(48)@ midstate followed by a 22-byte ADRS and the input, so
-- each F or H is one SHA-256 compression; in Simplicity the ADRS fields are
-- appended with the SHA-256 context jets.
module JetDiscovery.Corpus.Shrincs
  ( entries
  , maxDepth
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import Data.Bits (testBit)
import qualified Data.Word as DW
import qualified Data.List as L

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (scribe, eq)
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.Word as Word
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Simplicity, Primitive)
import Simplicity.Bitcoin.Primitive (PrimEnv)
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Ty.Word

import JetDiscovery.Corpus.Apps (sigMsg)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.Kernels (wotsChain)
import JetDiscovery.Lib.TxSer (ctxWith)
import JetDiscovery.Lib.HashSigWitness (pair8,pair32,fieldItems)
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Shrincs as Ref
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import Simplicity.Bitcoin.Jets (unwrap)

-- | Largest supported authentication path (leaf depth).  The FXMSS tree may be
-- up to 255 deep; loops are unrolled to this bound.
maxDepth :: Int
maxDepth = 8

w128FromBytes :: BS.ByteString -> Word128
w128FromBytes = toWord128 . BS.foldl' (\a b -> a * 256 + toInteger b) 0

w512FromBytes :: BS.ByteString -> Word512
w512FromBytes = toWord512 . BS.foldl' (\a b -> a * 256 + toInteger b) 0

-- | Select the left or right half of a pair of equal types.
pick :: (Core term, TyC x, TyC c) => Bool -> term x c -> term (x, x) c
pick True = drop
pick False = take

-- | Nibble @k@ (0 = most significant) of a 128-bit word, as in base_2b(x, 4, 32).
nibble :: (Core term) => Int -> term Word128 Word4
nibble k = pick (testBit k 4) (pick (testBit k 3) (pick (testBit k 2) (pick (testBit k 1) (pick (testBit k 0) iden))))

nib8 :: Core term => term Word4 Word8
nib8 = konst (toWord4 0) &&& iden

-- | Bit @k@ (0 = least significant) of a 64-bit word.
bit64 :: Core term => Int -> term Word64 Bit
bit64 k = pick (testBit p 5) (pick (testBit p 4) (pick (testBit p 3) (pick (testBit p 2) (pick (testBit p 1) (pick (testBit p 0) iden)))))
 where p = 63 - k

-- | Pair up a list of 2^n terms into a balanced tree of pairs (32 x Word128 -> Word4096).
tree32 :: (Core term, TyC a) => [term a Word128] -> term a Word4096
tree32 ts = p16 (L.take 16 ts) &&& p16 (L.drop 16 ts)
 where
  p16 xs = p8 (L.take 8 xs) &&& p8 (L.drop 8 xs)
  p8 xs = p4 (L.take 4 xs) &&& p4 (L.drop 4 xs)
  p4 xs = p2 (L.take 2 xs) &&& p2 (L.drop 2 xs)
  p2 [a, b] = a &&& b
  p2 _ = error "tree32"

data SW = SW { swPkSeed :: Word128, swSlRoot :: Word128, swSfRoot :: Word128, swR :: Word128, swH :: Word8, swIdx :: Word64, swCounter :: Word16, swChains :: [Word128], swAuth :: [Word128] }

type SFHeader=(Word128,(Word128,(Word128,Word128)))
type SFInput=(SFHeader,(Word8,(Word64,Word16)))

-- Bind the multiply-used seed/roots/R/height/index/counter header once.
-- Each independent chain/path value enters at its single consuming stage.
shrincsStateful :: forall term. (Simplicity term,Primitive term) => SW -> term () ()
shrincsStateful sw
 | length (swChains sw)/=32 || length (swAuth sw)/=maxDepth=error "SHRINCS stateful proof dimensions"
 | otherwise=witness packed >>> statefulT sw
 where
  packed=((swPkSeed sw,(swSlRoot sw,(swSfRoot sw,swR sw))),(swH sw,(swIdx sw,swCounter sw)))

appendT :: (Assert term,TyC a,TyC b) => term a b -> term (Ctx8,b) Ctx8 -> term (a,Ctx8) (a,Ctx8)
appendT f jet=oh &&& ((ih &&& (oh >>> f)) >>> jet)
hashStart :: (Assert term,TyC a) => term a (a,Ctx8)
hashStart=iden &&& (unit >>> ctx8Init)
hashEnd :: (Assert term,TyC a) => term (a,Ctx8) Word256
hashEnd=drop ctx8Finalize

statefulT :: forall term. (Simplicity term,Primitive term) => SW -> term SFInput ()
statefulT sw=checks &&& (rootOk &&& sumOk) >>> unit
 where
  pkSeedT=oh >>> oh
  slRootT=oh >>> ih >>> oh
  sfRootT=oh >>> ih >>> ih >>> oh
  randomizer=oh >>> ih >>> ih >>> ih
  h=ih >>> oh
  idx=ih >>> ih >>> oh
  counter=ih >>> ih >>> ih
  chainValue i=witness (swChains sw!!i)
  authValue i=witness (swAuth sw!!i)
  k8 :: forall a. TyC a => Integer -> term a Word8
  k8=konst.w8
  mid :: term SFInput Ctx8
  mid=((unit >>> ctx8Init) &&& ((pkSeedT &&& konst (toWord128 0)) &&& konst (w256 0))) >>> ctx8Add64
  prefix ty=(iden &&& mid) >>> appendT h ctx8Add1 >>> appendT idx ctx8Add8 >>> appendT (k8 ty) ctx8Add1
  inner=hashStart >>> appendT randomizer ctx8Add16 >>> appendT pkSeedT ctx8Add16 >>> appendT sfRootT ctx8Add16
        >>> appendT h ctx8Add1 >>> appendT idx ctx8Add8 >>> appendT (konst (w16 0)) ctx8Add2 >>> appendT slRootT ctx8Add16 >>> appendT (unit >>> sigMsg) ctx8Add32 >>> hashEnd
  digest=hashStart >>> appendT randomizer ctx8Add16 >>> appendT pkSeedT ctx8Add16 >>> appendT inner ctx8Add32
         >>> appendT h ctx8Add1 >>> appendT idx ctx8Add8 >>> hashEnd
  hashed=prefix 22 >>> appendT digest ctx8Add32 >>> appendT (konst (w32 0)) ctx8Add4 >>> appendT counter ctx8Add2 >>> hashEnd >>> oh
  sumOk=hashed >>> (foldl (\acc k -> acc &&& (nibble k >>> nib8 >>> (konst (w8 0) &&& iden)) >>> Arith.add word16 >>> ih) (konst (w16 0)) [0..31] &&& konst (w16 (toInteger Ref.constantSum))) >>> eq >>> verify
  pre16=prefix 16 >>> appendT (konst (w32 0)) ctx8Add4 >>> ih
  chain i=(((pre16 &&& konst (w32 (toInteger i))) >>> ctx8Add4) &&& ((hashed >>> nibble i) &&& chainValue i)) >>> wotsChain
  tips=tree32 [chain i | i<-[0..31]]
  leafPk=prefix 17 >>> appendT (konst (w64 0)) ctx8Add8 >>> appendT (konst (w32 0)) ctx8Add4 >>> appendT tips ctx8Add512 >>> hashEnd >>> oh
  root=(iden &&& leafPk) >>> L.foldl' (>>>) iden [level k | k<-[0..maxDepth-1]] >>> ih
  level :: Int -> term (SFInput,Word128) (SFInput,Word128)
  level k=(((oh >>> h) &&& k8 (254-toInteger k)) >>> Arith.le word8) &&& iden >>> cond (oh &&& hk) iden
   where
    parentH=((oh >>> h) &&& k8 (toInteger k+1)) >>> Arith.add word8 >>> ih
    parentI=(k8 (toInteger k+1) &&& (oh >>> idx)) >>> Word.right_shift word8 word64
    ordered=(((oh >>> idx >>> bit64 k)) &&& (ih &&& (oh >>> authValue k))) >>> cond (ih &&& oh) iden
    prefixH=(iden &&& (oh >>> mid)) >>> appendT parentH ctx8Add1 >>> appendT parentI ctx8Add8 >>> appendT (k8 18) ctx8Add1
            >>> appendT (konst (w64 0)) ctx8Add8 >>> appendT (konst (w32 0)) ctx8Add4
    hk=prefixH >>> appendT ordered ctx8Add32 >>> hashEnd >>> oh
  rootOk=(root &&& sfRootT) >>> eq >>> verify
  depthOk=(k8 (255-toInteger maxDepth) &&& h) >>> Arith.le word8 >>> verify
  indexBound=(idx &&& konst (w64 (2^maxDepth))) >>> Arith.lt word64 >>> verify
  indexBits=foldr (\k acc -> (bitOk k &&& acc) >>> unit) unit [0..maxDepth-1]
  bitOk k=((idx >>> bit64 k) &&& iden) >>> cond ((h &&& k8 (254-toInteger k)) >>> Arith.le word8 >>> verify) unit
  statefulOk=(h &&& k8 254) >>> Arith.le word8 >>> verify
  checks=((statefulOk &&& depthOk) &&& (indexBound &&& indexBits)) >>> unit

-- Vectors ----------------------------------------------------------------------

entries :: [Entry]
entries =
  [ Entry
    { entryId = "pq-shrincs-stateful"
    , entryTitle = "SHRINCS stateful signature on sig_all_hash (WOTS+C + FXMSS path up to depth " ++ show maxDepth ++ ")"
    , entrySpec = "SHRINCS draft (vendor-specs/shrincs/SHRINCS.md, shrincs_verify stateful branch)"
    , entryCategory = PostQuantum
    , entryVectorSource = Derived "signatures from JetDiscovery.Ref.Shrincs, a transcription of the spec's Python; upstream vectors are published only as SHA-256 fingerprints"
    , entryAssumptions = [ "leaf depth at most " ++ show maxDepth ++ " (the FXMSS tree allows 255); each extra level adds one H call"
                         , "message = sig_all_hash, empty context"
                         , "the static bound counts 15 F calls per chain (480), although WOTS+C's constant sum makes verification do exactly 240" ]
    , entryProgram = \sw -> Prog (shrincsStateful sw)
    , entryVectors =
        [ Vector ("valid, leaf depth " ++ show d ++ ", index " ++ show i ++ refNote d i) env (swOf d i) Accept | (d, i) <- cases ] ++
        [ Vector "same-CMR corrupted chain value" env ((swOf 4 5) { swChains = w128 0 : L.drop 1 (swChains (swOf 4 5)) }) Reject
        , Vector "same-CMR wrong grinding counter" env ((swOf 4 5) { swCounter = w16 (toInteger (fromWord16 (swCounter (swOf 4 5))) + 1) }) Reject
        , Vector "same-CMR wrong authentication path node" env ((swOf 8 200) { swAuth = w128 1 : L.drop 1 (swAuth (swOf 8 200)) }) Reject
        , Vector "same-CMR seed header splice" env ((swOf 4 5) {swPkSeed=w128 0}) Reject
        , Vector "same-CMR randomizer header splice" env ((swOf 4 5) {swR=w128 0}) Reject
        , Vector "signature for another transaction" env2 (swOf 1 0) Reject
        , Vector "leaf index too large for its depth" env ((swOf 4 5) { swIdx = w64 21 }) Reject
        ]
    }
  ]
 where
  cases = [(1, 0), (1, 1), (4, 5), (6, 0), (8, 200)]
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xffffffff] [mkOutput 99000 (unhex "0014" <> BS.replicate 20 1)] 0) 0 defaultTap
  env2 = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xffffffff] [mkOutput 98000 (unhex "0014" <> BS.replicate 20 1)] 0) 0 defaultTap
  seeds = (BS.replicate 16 0x5e, BS.replicate 16 0x9f, BS.replicate 16 0x7a)
  slRoot = BS.replicate 16 0x51
  authFor d = [ BS.replicate 16 (fromIntegral (0x30 + k)) | k <- [1 .. d] ]
  dummySW = SW (w128 0) (w128 0) (w128 0) (w128 0) (w8 254) (w64 0) (w16 0) (replicate 32 (w128 0)) (replicate maxDepth (w128 0))
  cmr = progCmr (Prog (shrincsStateful dummySW))
  msgOf = maybe (error "shrincs env") (\e -> maybe (error "sighash") w256ToBytes (Jets.fastEval (unwrap (Jets.jetSubst SigHash.sigAllHash)) e ())) (env cmr)
  signed d i = Ref.signStateful seeds slRoot d i (authFor d) msgOf
  -- the Haskell reference verifier must accept every positive vector too
  refNote d i = let (s, pub) = signed d i in if Ref.verifyStateful msgOf (Ref.sigBytes s) pub then "" else " (REFERENCE REJECTS)"
  swOf d i = let (s, pub) = signed d i in
    SW (w128FromBytes (BS.take 16 pub)) (w128FromBytes (BS.take 16 (BS.drop 16 pub))) (w128FromBytes (BS.drop 32 pub))
       (w128FromBytes (Ref.ssR s)) (w8 (toInteger (Ref.ssHeight s))) (w64 (Ref.ssIndex s)) (w16 (toInteger (Ref.ssCounter s)))
       (map w128FromBytes (Ref.ssChains s)) (L.take maxDepth (map w128FromBytes (Ref.ssAuth s) ++ repeat (w128 0)))
  w128 = toWord128
