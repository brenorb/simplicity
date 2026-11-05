{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
-- | The remaining open script-extension proposals:
--
-- * BIP 98 / BIP 116 MERKLEBRANCHVERIFY: Merkle branches with fast-SHA256
--   (one SHA-256 compression from a custom IV, no padding).
-- * BIP 117 tail-call execution, which Simplicity provides as delegation
--   ('disconnect'): run a witness-supplied program whose CMR a key signed.
-- * BIP 360 P2MR: a covenant that output 0 is a P2MR output whose script tree
--   contains a given Simplicity leaf (post-quantum migration).
-- * BIP 441 restored big-number arithmetic: a 256-bit modular multiplication
--   with an arbitrary modulus (a 512-bit product and a 512-bit division).
-- * BIP 449 OP_TWEAKADD: x(P + tG), with the BIP's own test vectors.
-- * TAPLEAF_UPDATE_VERIFY (TLUV, bitcoin-dev 2021, no BIP number): the output
--   at this input's index re-creates this input's taproot with the current leaf
--   removed and the internal key updated by adding a key.
module JetDiscovery.Corpus.MoreBips
  ( entries
  , fastSha256Iv
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import Data.Bits (testBit)
import qualified Data.List as L
import qualified Data.Word as DW

import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import qualified Simplicity.Programs.Bitcoin.Lib as BLib
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.Term (Simplicity, Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import Simplicity.Bitcoin.Primitive (PrimEnv)
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.MerkleRoot (CommitmentRoot, commitmentRoot)
import Simplicity.LibSecp256k1.Schnorr (PubKey(..), Sig(..))
import Simplicity.Ty.Word

import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Ref

type SigW = (Word256, Word256)

anyEnv :: Hash256 -> Maybe PrimEnv
anyEnv = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xfffffffe] [mkOutput 99000 (unhex "0014" <> BS.replicate 20 1)] 300) 0 defaultTap

w32of :: BS.ByteString -> Word256
w32of = w256FromBytes

-- BIP 98 / 116 ---------------------------------------------------------------------

-- | The fast-SHA256 IV: the midstate after compressing BIP 98's 64-byte constant from SHA-256's IV.
fastSha256Iv :: Integer
fastSha256Iv = 0x89cc59c6f7ce43fcf612670e78e9362e768fd2c918bd42ed0e0b9f79eef68a24

-- | Verify a Merkle branch of up to 'mbDepth' levels: input ((leaf, root)) with the path as witness.
-- Each level is (present?, (sibling on the left?, sibling)).
mbDepth :: Int
mbDepth = 16

merkleBranch :: (Assert term, Witness term) => [Maybe (Bool, BS.ByteString)] -> term (Word256, Word256) ()
merkleBranch path = (take walk &&& ih) >>> eq >>> verify
 where
  fast = konst (toWord256 fastSha256Iv) &&& iden >>> hashBlock
  step lvl = witness (maybe (Left ()) (\(l, s) -> Right (if l then Right () else Left (), w32of s)) lvl) &&& iden >>> match ih level
  -- input ((sibling-left bit, sibling), node)
  level = (ooh &&& (oih &&& ih)) >>> cond (fast) (ih &&& oh >>> fast)
  walk = foldr (\lvl k -> step lvl >>> k) iden path

fastRef :: BS.ByteString -> BS.ByteString -> BS.ByteString
fastRef a b = maybe (error "fastRef") w256ToBytes (Jets.fastEval (konst (toWord256 fastSha256Iv) &&& iden >>> hashBlock) env (toWord512 (Ref.intFromBytes (a <> b))))
 where Just env = anyEnv (hashFromInteger 0)

-- BIP 117 --------------------------------------------------------------------------

-- | Tail call: a key signs the CMR of a delegated program supplied at spend time.
tailCall :: (Simplicity term, Primitive term) => Word256 -> SigW -> (forall t. (Simplicity t, Primitive t) => t () ()) -> term () ()
tailCall pk sig sub = disconnect body sub >>> unit
 where
  -- input (CMR of the delegated program, ())
  body = ((konst pk &&& oh) &&& witness sig >>> Secp.bip_0340_verify) &&& unit

delegatedA, delegatedB :: (Simplicity t, Primitive t) => t () ()
delegatedA = konst (w32 200) >>> TL.checkLockHeight      -- spendable after height 200
delegatedB = konst (w32 400) >>> TL.checkLockHeight      -- not yet: the vector transaction's locktime is 300

subCmr :: (forall t. (Simplicity t, Primitive t) => t () ()) -> BS.ByteString
subCmr sub = hashToBytes (commitmentRoot' (unwrap (Jets.jetSubst sub)))
 where commitmentRoot' x = commitmentRoot (x :: CommitmentRoot () ())

-- BIP 360 --------------------------------------------------------------------------

-- | Output 0 is P2MR (OP_2 <root>) and the tree contains this Simplicity leaf (CMR given):
-- the root is rebuilt from the leaf with the witness Merkle path (BIP 341 sorted TapBranch hashing).
p2mrOutput :: (Assert term, Primitive term, Witness term) => Word256 -> [Maybe BS.ByteString] -> term () ()
p2mrOutput leafCmr path = scriptHash &&& (konst (w32 0) >>> primitive Prim.OutputScriptHash >>> verify) >>> eq >>> verify
 where
  leaf = witness leafCmr >>> BLib.buildTapleafSimplicity
  step lvl = witness (maybe (Left ()) (Right . w32of) lvl) &&& iden >>> match ih (BLib.buildTapbranch)
  root = leaf >>> foldr (\lvl k -> step lvl >>> k) iden path
  scriptHash = ((unit >>> ctx8Init) &&& konst (w16 0x5220) >>> ctx8Add2) &&& root >>> ctx8Add32 >>> ctx8Finalize

tapleafRef :: BS.ByteString -> BS.ByteString
tapleafRef cmr = hashToBytes (taggedSha256 "TapLeaf" (BS.pack [0xbe, 32] <> cmr))

tapbranchRef :: BS.ByteString -> BS.ByteString -> BS.ByteString
tapbranchRef a b = hashToBytes (taggedSha256 "TapBranch" (if a < b then a <> b else b <> a))

-- BIP 441 --------------------------------------------------------------------------

-- | (a * b) mod m for 256-bit operands (OP_MUL / OP_MOD on restored big numbers).
modMul256 :: Assert term => term ((Word256, Word256), (Word256, Word256)) ()
modMul256 = ((konst (toWord256 0) &&& ioh) >>> Arith.lt word256 >>> verify) &&& remainderOk >>> unit
 where
  remainderOk = (((ooh &&& oih >>> Arith.multiply word256) &&& (konst (toWord256 0) &&& ioh) >>> Arith.div_mod word512 >>> ih >>> ih) &&& iih) >>> eq >>> verify
-- input ((a, b), (m, expected)); the product (Word512) is divided by (0, m); the remainder's low half is the result

-- BIP 449 --------------------------------------------------------------------------

-- | x(P + tG) == expected: input ((t, x(P)), expected).
tweakAdd :: Assert term => term ((Word256, Word256), Word256) ()
tweakAdd = (take q &&& ih) >>> eq >>> verify
 where
  -- t must be below the group order: scalar_normalize must not change it
  tOk = (oh &&& (oh >>> Secp.scalar_normalize) >>> eq >>> verify)
  lift = ih >>> Secp.pubkey_unpack >>> verify >>> Secp.decompress >>> verify
  q = tOk &&& ((oh >>> Secp.scalar_normalize >>> Secp.generate) &&& lift >>> Secp.gej_ge_add >>> Secp.gej_normalize >>> verify >>> oh) >>> ih

-- TLUV -----------------------------------------------------------------------------

-- | The output at this input's index pays P2TR(taptweak(P + X, root')), where P is this input's internal
-- key, X a key given by the spender, and root' this input's script tree with the current leaf removed
-- (its sibling path[0] takes its place).  Depth 1..maxDepth handled by folding the remaining path.
tluvDepth :: Int
tluvDepth = 8

tluv :: (Assert term, Primitive term, Witness term) => Word256 -> term () ()
tluv x = (outKey >>> p2trHash) &&& (unit >>> primitive Prim.CurrentIndex >>> primitive Prim.OutputScriptHash >>> verify) >>> eq >>> verify
 where
  liftX t = (false &&& t) >>> Secp.decompress >>> verify
  -- P + X: P as a Jacobian point with z = 1
  newKey = ((liftX (unit >>> primitive Prim.InternalKey) &&& konst (toWord256 1)) &&& liftX (witness x)) >>> Secp.gej_ge_add >>> Secp.gej_normalize >>> verify >>> oh
  path i = konst (w8 (toInteger i)) >>> primitive Prim.Tappath
  -- root' = fold over path[1..] starting from path[0]; absent entries end the path
  root' = (path 0 >>> verify) >>> foldr (\i k -> (iden &&& (unit >>> path i)) >>> (ih &&& oh) >>> match ih (ih &&& oh >>> BLib.buildTapbranch) >>> k) iden [1 .. tluvDepth - 1]
  outKey = newKey &&& root' >>> BLib.buildTaptweak
  p2trHash = ((unit >>> ctx8Init) &&& konst (w16 0x5120) >>> ctx8Add2) &&& iden >>> ctx8Add32 >>> ctx8Finalize

-- Vectors ------------------------------------------------------------------------

sk1 :: Integer
sk1 = 0xB7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF

entries :: IO [Entry]
entries = do
  twVecs <- loadTweakAdd
  return
    [ Entry
      { entryId = "bip116-merklebranchverify"
      , entryTitle = "MERKLEBRANCHVERIFY: fast-SHA256 Merkle branch of up to 16 levels"
      , entrySpec = "BIP 116 with BIP 98 fast Merkle trees (vendor-specs/bips/bip-0116.mediawiki, bip-0098.mediawiki)"
      , entryCategory = CovenantBip
      , entryVectorSource = Derived "roots computed with the Sha256Block jet implementation from BIP 98's IV (the IV is checked against BIP 98's midstate in cabal test)"
      , entryAssumptions = ["single-leaf branch proofs (one VERIFY hash, SKIP hashes along the path) of depth at most 16", "leaf, root and path are witness operands"]
      , entryProgram = \((leaf, root), path) -> Prog (witness (w32of leaf, w32of root) >>> merkleBranch path)
      , entryVectors =
          [ Vector ("depth " ++ show d) anyEnv ((leafH, rootOf p), pad p) Accept | d <- [1, 5, 16], let p = pathOf d ] ++
          [ Vector "tampered sibling" anyEnv ((leafH, rootOf (pathOf 5)), pad (tamper (pathOf 5))) Reject
          , Vector "sibling on the wrong side" anyEnv ((leafH, rootOf (pathOf 5)), pad (flipSide (pathOf 5))) Reject ]
      }
    , Entry
      { entryId = "bip117-tail-call"
      , entryTitle = "Tail call / delegation: run a program whose CMR the owner signed"
      , entrySpec = "BIP 117 (vendor-specs/bips/bip-0117.mediawiki), as Simplicity delegation with disconnect"
      , entryCategory = CovenantBip
      , entryVectorSource = Derived "BIP 340 signatures on the delegated program's CMR"
      , entryAssumptions = ["the delegated program is supplied at spend time; its CMR is signed by the owner key"]
      , entryProgram = \(which, sig) -> Prog (if which then tailCall pk1 sig delegatedA else tailCall pk1 sig delegatedB)
      , entryVectors =
          [ Vector "signed delegate, its timelock satisfied" anyEnv (True, sigOn (subCmr delegatedA)) Accept
          , Vector "signed delegate, its timelock not satisfied" anyEnv (False, sigOn (subCmr delegatedB)) Reject
          , Vector "delegate not signed (signature for another delegate)" anyEnv (True, sigOn (subCmr delegatedB)) Reject ]
      }
    , Entry
      { entryId = "bip360-p2mr-output"
      , entryTitle = "P2MR covenant: output 0 is a P2MR tree containing a given Simplicity leaf"
      , entrySpec = "BIP 360 (vendor-specs/bips/bip-0360.mediawiki)"
      , entryCategory = CovenantBip
      , entryVectorSource = Derived "P2MR roots from tagged-hash references of BIP 341 TapLeaf/TapBranch"
      , entryAssumptions = ["Simplicity leaf version 0xbe; Merkle path of at most 8 levels as witness", "the leaf CMR is a witness operand"]
      , entryProgram = \(cmr, p) -> Prog (p2mrOutput (w32of cmr) p)
      , entryVectors =
          [ Vector ("depth " ++ show d) (p2mrEnv (p2mrRoot p)) (leafCmr, padN 8 p) Accept | d <- [0, 1, 3, 8], let p = p2mrPath d ] ++
          [ Vector "output commits to another tree" (p2mrEnv (BS.replicate 32 7)) (leafCmr, padN 8 (p2mrPath 3)) Reject
          , Vector "different leaf CMR at the same output" (p2mrEnv (p2mrRoot (p2mrPath 3))) (BS.replicate 32 7, padN 8 (p2mrPath 3)) Reject
          , Vector "P2TR instead of P2MR" (\c -> mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 (unhex "5120" <> p2mrRoot (p2mrPath 3))] 0) 0 defaultTap c) (leafCmr, padN 8 (p2mrPath 3)) Reject ]
      }
    , Entry
      { entryId = "bip441-bignum-modmul"
      , entryTitle = "Restored big-number arithmetic: 256-bit (a * b) mod m"
      , entrySpec = "BIP 441 (vendor-specs/bips/bip-0441.mediawiki): OP_MUL and OP_MOD on large numbers"
      , entryCategory = CovenantBip
      , entryVectorSource = Derived "expected values from Haskell Integer arithmetic"
      , entryAssumptions = ["256-bit operands and modulus (BIP 441 allows larger numbers, bounded by its varops budget)"]
      , entryProgram = \((a, b), (m, r)) -> Prog (witness ((toWord256 a, toWord256 b), (toWord256 m, toWord256 r)) >>> modMul256)
      , entryVectors =
          [ Vector ("case " ++ show i) anyEnv ((a, b), (m, a * b `mod` m)) Accept | (i, (a, b, m)) <- zip [1 :: Int ..] mmCases ] ++
          [ Vector "wrong remainder" anyEnv ((5, 7), (11, 3)) Reject
          , Vector "zero modulus" anyEnv ((5, 7), (0, 35)) Reject ]
      }
    , Entry
      { entryId = "bip449-tweakadd"
      , entryTitle = "OP_TWEAKADD: x(P + tG)"
      , entrySpec = "BIP 449 (vendor-specs/bips/bip-0449.md)"
      , entryCategory = CovenantBip
      , entryVectorSource = Upstream ("vendor-specs/bips/bip-0449.md, \"Test vectors (Generated)\": " ++ show (length twVecs) ++ " cases")
      , entryAssumptions = ["tweak, key and expected result are witness operands"]
      , entryProgram = \((t, p), q) -> Prog (witness ((w32of t, w32of p), w32of q) >>> tweakAdd)
      , entryVectors = twVecs
      }
    , Entry
      { entryId = "tluv-remove-leaf"
      , entryTitle = "TAPLEAF_UPDATE_VERIFY: remove the current leaf and add a key to the internal key"
      , entrySpec = "TLUV (A. Towns, bitcoin-dev, September 2021; no BIP number)"
      , entryCategory = CovenantBip
      , entryVectorSource = Derived "output keys from Ref.Bip340 point arithmetic and BIP 341 tagged hashes"
      , entryAssumptions = [ "this input's taproot path has 1 to " ++ show tluvDepth ++ " levels; the output at the same index must re-create it"
                           , "key update by point addition of a spender-given x-only key (even y, a witness operand); amounts not checked" ]
      , entryProgram = \x -> Prog (tluv (w256 x))
      , entryVectors =
          [ Vector ("remove leaf at depth " ++ show d) (tluvEnv d True) tluvX Accept | d <- [1, 2, 5] ] ++
          [ Vector "output keeps the removed leaf" (tluvEnv 3 False) tluvX Reject
          , Vector "different key added" (tluvEnv 3 True) (Ref.pubkeyOf 99) Reject ]
      }
    ]
 where
  -- BIP 116
  leafH = BS.replicate 32 0xab
  pathOf d = [ (odd i, BS.replicate 32 (fromIntegral i)) | i <- [1 .. d] ]
  rootOf = L.foldl' (\cur (l, s) -> if l then fastRef s cur else fastRef cur s) leafH
  pad p = L.take mbDepth (map Just p ++ repeat Nothing)
  tamper ((l, _):r) = (l, BS.replicate 32 0) : r
  tamper [] = []
  flipSide ((l, s):r) = (l == False, s) : r
  flipSide [] = []
  -- BIP 117
  pk1 = w256 (Ref.pubkeyOf sk1)
  sigOn cmr = let Sig r s = signMsg sk1 cmr in (toWord256 (toInteger r), toWord256 (toInteger s))
  -- BIP 360
  leafCmr = BS.replicate 32 0x3d
  p2mrPath d = [ BS.replicate 32 (fromIntegral (0x40 + i)) | i <- [1 .. d] ]
  p2mrRoot p = L.foldl' tapbranchRef (tapleafRef leafCmr) p
  padN n p = L.take n (map Just p ++ repeat Nothing)
  p2mrEnv root = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 (unhex "5220" <> root)] 0) 0 defaultTap
  -- BIP 441
  mmCases = [ (3, 5, 7), (2 ^ (255 :: Int) + 19, 2 ^ (200 :: Int) + 7, 2 ^ (255 :: Int) - 19)
            , (2 ^ (256 :: Int) - 1, 2 ^ (256 :: Int) - 1, 2 ^ (256 :: Int) - 189), (123456789, 987654321, 1000000007) ]
  -- TLUV
  tluvX = Ref.pubkeyOf 7
  ownLeaf = BS.replicate 32 0x66
  tluvPath d = [ BS.replicate 32 (fromIntegral (0x10 + i)) | i <- [1 .. d] ]
  tluvEnv d removed c =
    let p = tluvPath d
        ik = Ref.pubkeyOf sk1
        newRoot = if removed then L.foldl' tapbranchRef (head p) (L.drop 1 p) else L.foldl' tapbranchRef ownLeaf p
        newKey = Ref.xOnly (Ref.pointAdd (Ref.liftX ik) (Ref.liftX tluvX))
        outKey = Ref.taprootTweak newKey newRoot
        tap = (defaultTap c) { tapInternalKey = PubKey (fromInteger ik), tappath = map hashFromBytes p }
    in mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 (unhex "5120" <> Ref.bytesFromInt outKey)] 0) 0 (const tap) c

-- | Parse BIP 449's generated vectors (passing and failing cases).
loadTweakAdd :: IO [JetDiscovery.Types.Vector ((BS.ByteString, BS.ByteString), BS.ByteString)]
loadTweakAdd = do
  s <- readFile "vendor-specs/bips/bip-0449.md"
  let ls = lines s
      val k l = let (a, b) = break (== '=') l in if takeWhile (/= ' ') (L.dropWhile (== ' ') a) == k then Just (filter (/= ' ') (L.drop 1 b)) else Nothing
      go (l:rest) | Just pk <- val "pubkey32" l =
        let t = head [ v | Just v <- map (val "tweak32") rest ]
            e = head [ v | Just v <- map (val "expect") rest ]
        in (pk, t, e) : go (L.drop 2 rest)
      go (_:rest) = go rest
      go [] = []
      cases = go ls
  return [ Vector ("BIP 449 case " ++ show i ++ (if e == "fail" then " (must fail)" else ""))
                  anyEnv ((unhex t, unhex pk), if e == "fail" then BS.replicate 32 0 else unhex e)
                  (if e == "fail" then Reject else Accept)
         | (i, (pk, t, e)) <- zip [1 :: Int ..] cases ]
