-- | Smaller script-extension proposals:
--
-- * BIP 118 SIGHASH_ANYPREVOUT: a signature hash mode that omits the spent outpoint.
-- * BIP 349 OP_INTERNALKEY: check a signature against the taproot internal key.
-- * BIP 442 OP_PAIRCOMMIT: tagged hash of two length-prefixed byte strings.
-- * BIP 443 OP_CHECKCONTRACTVERIFY (CHECK_OUTPUT mode): an output's taproot
--   key equals a naked key tweaked with data and then with a taptree root.
module JetDiscovery.Corpus.CovenantMisc
  ( entries
  , apoMode
  , ccvOutputKey
  , embedDataT
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Serialize (runPut, put)
import qualified Data.Vector as V
import qualified Data.Word as DW

import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (scribe, eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Sha256.Lib
import Simplicity.Programs.CheckSig.Lib (checkSigVerify, checkSigVerify', sigHash')
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import qualified Simplicity.Programs.Bitcoin.Lib as BLib
import Simplicity.Bitcoin.Term (Simplicity, Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import Simplicity.Bitcoin.Primitive (PrimEnv)
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.LibSecp256k1.Schnorr (PubKey(..), Sig(..))
import Simplicity.Ty.Word

import JetDiscovery.Corpus.Baseline (signMsg, signSigAll)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer (ctxWith)
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Ref

-- BIP 118 ---------------------------------------------------------------------

-- | ANYPREVOUT-style signature hash mode: commits to the transaction and to this
-- input's value, script, sequence and tapleaf, but not to any outpoint.
apoMode :: (Assert term, Primitive term) => term () Word256
apoMode = ctx8InitTag "Simplicity/AnyPrevout"
      >>> ctxWith (primitive Prim.Version) ctx8Add4
      >>> ctxWith (primitive Prim.LockTime) ctx8Add4
      >>> ctxWith SigHash.outputsHash ctx8Add32
      >>> ctxWith Tx.currentValue ctx8Add8
      >>> ctxWith Tx.currentScriptHash ctx8Add32
      >>> ctxWith Tx.currentSequence ctx8Add4
      >>> ctxWith SigHash.tapleafHash ctx8Add32
      >>> ctx8Finalize

apoMessage :: PrimEnv -> BS.ByteString
apoMessage env = maybe (error "apoMessage") (Ref.bytesFromInt . fromWord256) $
  Jets.fastEval (sigHash' (unwrap (Jets.jetSubst apoMode))) env ()

-- BIP 349 ---------------------------------------------------------------------

-- | Signature check against the taproot internal key, over sig_all_hash.
internalKeySpend :: (Simplicity term, Primitive term) => (Word256, Word256) -> term () ()
internalKeySpend sig = (primitive Prim.InternalKey &&& disconnect iden (unwrap (Jets.jetSubst SigHash.sigAllHash))) &&& witness sig
                   >>> checkSigVerify

-- BIP 442 ---------------------------------------------------------------------

-- | hash_PairCommit(compact_size(len x1) || x1 || compact_size(len x2) || x2) == h
pairCommit :: Assert term => term ((Buffer511 Word8, Buffer511 Word8), Word256) ()
pairCommit = hashPC &&& ih >>> eq >>> verify
 where
  hashPC = ((unit >>> ctx8InitTag "PairCommit") &&& ooh >>> ctxAddVarString511) &&& oih >>> ctxAddVarString511 >>> ctx8Finalize

pairCommitRef :: BS.ByteString -> BS.ByteString -> BS.ByteString
pairCommitRef a b = hashToBytes (taggedSha256 "PairCommit" (ser a <> ser b))
 where ser x = runPut (putCompactSize (fromIntegral (BS.length x))) <> x

-- BIP 443 ---------------------------------------------------------------------

-- | Output key for naked key @pk@, data @d@ and taptree root @r@: input ((pk, d), r).
ccvOutputKey :: Assert term => term ((Word256, Word256), Word256) Word256
ccvOutputKey = (take embedDataT &&& ih) >>> BLib.buildTaptweak

-- | BIP 443 @tweak_embed_data(pk, d)@ for 32-byte data: x(lift_x(pk) + sha256(pk || d) G).
embedDataT :: Assert term => term (Word256, Word256) Word256
embedDataT = (t >>> Secp.generate) &&& liftX >>> Secp.gej_ge_add >>> Secp.gej_normalize >>> verify >>> oh
 where
  t = ((unit >>> ctx8Init) &&& oh >>> ctx8Add32) &&& ih >>> ctx8Add32 >>> ctx8Finalize >>> Secp.scalar_normalize
  liftX = (false &&& oh) >>> Secp.decompress >>> verify

-- | CCV in CHECK_OUTPUT mode for one input: input (((index, (pk, d)), r)).
ccvCheckOutput :: (Assert term, Primitive term) => term ((Word32, (Word256, Word256)), Word256) ()
ccvCheckOutput = scriptOk &&& amountOk >>> unit
 where
  key = (take (drop iden) &&& ih) >>> ccvOutputKey
  -- sha256(0x51 0x20 || key) == output_script_hash(index)
  scriptHash = ((unit >>> ctx8Init) &&& (unit >>> scribe (w16 0x5120)) >>> ctx8Add2) &&& key >>> ctx8Add32 >>> ctx8Finalize
  scriptOk = scriptHash &&& (ooh >>> primitive Prim.OutputScriptHash >>> verify) >>> eq >>> verify
  -- the output carries at least this input's value (single-input version of the default amount semantic)
  amountOk = (unit >>> Tx.currentValue) &&& (ooh >>> primitive Prim.OutputValue >>> verify) >>> Arith.le word64 >>> verify

-- Vectors -------------------------------------------------------------------

sk1 :: Integer
sk1 = 0xB7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF

pk1 :: Integer
pk1 = Ref.pubkeyOf sk1

txWith :: Outpoint -> DW.Word64 -> DW.Word64 -> BS.ByteString -> SigTx
txWith op inVal outVal outScript = mkTx 2 [mkInput op inVal (BSL.fromStrict (unhex "5120" <> BS.replicate 32 9)) 0xfffffffe] [mkOutput outVal outScript] 0

entries :: [Entry]
entries =
  [ Entry
    { entryId = "bip118-apo"
    , entryTitle = "SIGHASH_ANYPREVOUT-style rebindable signature"
    , entrySpec = "BIP 118 (vendor-specs/bips/bip-0118.mediawiki), as a Simplicity signature hash mode"
    , entryCategory = CovenantBip
    , entryVectorSource = Derived "BIP 340 signatures over the APO-mode message, made with JetDiscovery.Ref.Bip340"
    , entryAssumptions = [ "the APO digest commits to version, locktime, outputs_hash, this input's value, script hash, sequence and tapleaf hash"
                         , "not hash-compatible with BIP 118's BIP 341-style digest (Simplicity signatures use their own sighash modes)" ]
    , entryProgram = \sig -> Prog (checkSigVerify' (unwrap (Jets.jetSubst apoMode)) (PubKey (fromInteger pk1)) sig)
    , entryVectors =
        [ Vector "signature verifies on the transaction it was made for" (envA) apoSig Accept
        , Vector "same signature rebinds to a different outpoint" (envOp (Outpoint (hashFromInteger 0xbeef) 7)) apoSig Accept
        , Vector "different output value" (envOut 48000) apoSig Reject
        , Vector "different input value" (envVal 60000) apoSig Reject
        ]
    }
  , Entry
    { entryId = "bip349-internalkey"
    , entryTitle = "OP_INTERNALKEY: signature against the taproot internal key"
    , entrySpec = "BIP 349 (vendor-specs/bips/bip-0349.md)"
    , entryCategory = CovenantBip
    , entryVectorSource = Derived "sig_all_hash signatures made with JetDiscovery.Ref.Bip340"
    , entryAssumptions = ["the internal key is read with the existing internal_key jet"]
    , entryProgram = \(r, s) -> Prog (internalKeySpend (r, s))
    , entryVectors =
        [ Vector "internal key signs" ikEnv ikSig Accept
        , Vector "different internal key" ikEnvOther ikSig Reject ]
    }
  , Entry
    { entryId = "bip442-paircommit"
    , entryTitle = "OP_PAIRCOMMIT: tagged hash of two length-prefixed elements"
    , entrySpec = "BIP 442 (vendor-specs/bips/bip-0442.md)"
    , entryCategory = CovenantBip
    , entryVectorSource = Derived "expected hashes from a Haskell reference of the BIP 442 formula (no upstream vectors)"
    , entryAssumptions = ["elements of at most 511 bytes (Script allows 520)", "the two elements and the expected hash are witness operands"]
    , entryProgram = \((a, b), h) -> Prog (witness ((buffer511FromBytes a, buffer511FromBytes b), w256FromBytes h) >>> pairCommit)
    , entryVectors =
        [ Vector ("lengths " ++ show (BS.length a) ++ " and " ++ show (BS.length b)) anyEnv ((a, b), pairCommitRef a b) Accept
        | (a, b) <- pcCases ] ++
        [ Vector "swapped elements" anyEnv ((y, x), pairCommitRef x y) Reject | let (x, y) = pcCases !! 2 ] ++
        [ Vector "length prefix matters: (ab, c) vs (a, bc)" anyEnv ((BS.pack [1, 2], BS.pack [3]), pairCommitRef (BS.pack [1]) (BS.pack [2, 3])) Reject ]
    }
  , Entry
    { entryId = "bip443-ccv-output"
    , entryTitle = "OP_CHECKCONTRACTVERIFY, CHECK_OUTPUT mode with data and taptree"
    , entrySpec = "BIP 443 (vendor-specs/bips/bip-0443.mediawiki)"
    , entryCategory = CovenantBip
    , entryVectorSource = Derived "output keys from Haskell references of tweak_embed_data and taproot_tweak_pubkey"
    , entryAssumptions = [ "single input: the cross-input amount accounting of the default mode is not modelled"
                         , "32-byte data; data tweaks >= the group order are reduced instead of rejected (probability ~2^-128)"
                         , "the naked key is assumed to be a valid x coordinate below the field size"
                         , "index, naked key, data and taptree root are witness operands" ]
    , entryProgram = \((ix, (pk, d)), r) -> Prog (witness ((w32 ix, (w256 pk, w256FromBytes d)), w256FromBytes r) >>> ccvCheckOutput)
    , entryVectors =
        [ Vector "output matches the committed contract" (ccvEnv (ccvScript ccvData ccvRoot) 50000) ccvW Accept
        , Vector "output commits to different data" (ccvEnv (ccvScript (BS.replicate 32 3) ccvRoot) 50000) ccvW Reject
        , Vector "output has a different taptree" (ccvEnv (ccvScript ccvData (BS.replicate 32 4)) 50000) ccvW Reject
        , Vector "output value below the input value" (ccvEnv (ccvScript ccvData ccvRoot) 49999) ccvW Reject
        ]
    }
  ]
 where
  anyEnv = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  -- APO
  apoCmr = progCmr (Prog (checkSigVerify' (unwrap (Jets.jetSubst apoMode)) (PubKey (fromInteger pk1)) (Sig 0 0)))
  envGen op inVal outVal = mkEnv (txWith op inVal outVal (unhex "0014" <> BS.replicate 20 1)) 0 defaultTap
  envA = envGen (dummyOutpoint 0) 50000 49000
  envOp op = envGen op 50000 49000
  envOut v = envGen (dummyOutpoint 0) 50000 v
  envVal v = envGen (dummyOutpoint 0) v 49000
  apoSig = case envA apoCmr of
    Just e -> let msg = apoSighashMessage e in signMsg sk1 msg
    Nothing -> error "apo env"
  apoSighashMessage = apoMessage
  -- INTERNALKEY
  ikTap pk c = (defaultTap c) { tapInternalKey = PubKey (fromInteger pk) }
  ikTx = txWith (dummyOutpoint 0) 50000 49000 (unhex "0014" <> BS.replicate 20 1)
  ikEnv = mkEnv ikTx 0 (ikTap pk1)
  ikEnvOther = mkEnv ikTx 0 (ikTap Ref.nums)
  ikCmr = progCmr (Prog (internalKeySpend (w256 0, w256 0)))
  ikSig = case ikEnv ikCmr of
    Just e -> let Sig r s = signSigAll sk1 e in (toWord256 (toInteger r), toWord256 (toInteger s))
    Nothing -> error "ik env"
  -- PAIRCOMMIT
  pcCases = [ (BS.empty, BS.empty), (BS.pack [7], BS.empty), (BS.replicate 32 0xaa, BS.replicate 32 0xbb)
            , (BS.replicate 300 1, BS.replicate 17 2), (BS.replicate 511 3, BS.replicate 511 4) ]
  -- CCV
  ccvData = BS.replicate 32 0x11
  ccvRoot = BS.replicate 32 0x22
  ccvScript d r = unhex "5120" <> Ref.bytesFromInt (Ref.taprootTweak (Ref.embedData pk1 d) r)
  ccvEnv script outVal = mkEnv (txWith (dummyOutpoint 0) 50000 outVal script) 0 defaultTap
  ccvW = ((0, (pk1, ccvData)), ccvRoot)
