-- | Bitcoin applications: HTLC, 2-of-3 multisig, a vault with delayed
-- withdrawal and recovery, an oracle-settled contract for difference (DLC
-- style), and Merkle-tree key membership ("tree signatures", the main OP_CAT
-- motivation in BIP 347).
module JetDiscovery.Corpus.Apps
  ( entries
  , sigMsg
  , checkSigWith
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Prelude as P
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.List as L
import Data.Serialize (runPut, putWord64be)
import qualified Data.Word as DW

import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (scribe, eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Word (shift_const_by)
import Simplicity.Programs.Sha256.Lib
import Simplicity.Programs.CheckSig.Lib (sigHash')
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Bitcoin.Term (Simplicity, Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import Simplicity.Bitcoin.Primitive (PrimEnv)
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.LibSecp256k1.Schnorr (Sig(..), PubKey(..))
import Simplicity.Ty.Word

import JetDiscovery.Corpus.Baseline (signMsg, signSigAll, sigAllMessage)
import JetDiscovery.Corpus.Bip119Ctv (ctvNativeTemplate, ctvNativeRef)
import JetDiscovery.Corpus.CovenantMisc (embedDataT)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Ref

type SigW = (Word256, Word256)

-- | The signature message: the sig_all_hash jet's output, signed directly with
-- bip_0340_verify (as SimplicityHL programs do).
--
-- Note: 'Simplicity.Programs.CheckSig.sigHash'' would add about 150 WU, because
-- its two constants are written with 'scribe' at input type (Word256, Word256),
-- where the constant-word jets do not apply (see reports/mismatches.md).
sigMsg :: (Simplicity term, Primitive term) => term () Word256
sigMsg = unwrap (Jets.jetSubst SigHash.sigAllHash)

-- | The message 'sigMsg' evaluates to in an environment.
sigMsgValue :: PrimEnv -> BS.ByteString
sigMsgValue env = maybe (error "sigMsgValue") w256ToBytes (Jets.fastEval (unwrap (Jets.jetSubst SigHash.sigAllHash)) env ())

-- | BIP 340 check of signature @sig@ (an expression) by @pk@ on message @msg@.
checkSigWith :: (Assert term, TyC a) => Word256 -> term a Word256 -> term a SigW -> term a ()
checkSigWith pk msg sig = (konst pk &&& msg) &&& sig >>> Secp.bip_0340_verify

sha256Of32 :: Assert term => term Word256 Word256
sha256Of32 = (unit >>> ctx8Init) &&& iden >>> ctx8Add32 >>> ctx8Finalize

-- HTLC -------------------------------------------------------------------------

htlc :: (Simplicity term, Primitive term) => Word256 -> Word256 -> Word256 -> DW.Word32 -> Either (Word256, SigW) SigW -> term () ()
htlc h pkA pkB timeout w = witness w &&& sigMsg >>> match claim refund
 where
  -- ((preimage, sig), msg)
  claim = (take (take sha256Of32) &&& konst h >>> eq >>> verify) &&& checkSigWith pkA ih oih >>> unit
  -- (sig, msg)
  refund = (konst (w32 (toInteger timeout)) >>> TL.checkLockHeight) &&& checkSigWith pkB ih oh >>> unit

-- Multisig -----------------------------------------------------------------------

multisig2of3 :: (Simplicity term, Primitive term) => [Word256] -> [Maybe SigW] -> term () ()
multisig2of3 pks sigs = sigMsg >>> (slot 0 &&& (slot 1 &&& slot 2)) >>> maj >>> verify
 where
  slot i = witness (maybe (Left ()) Right (sigs !! i)) &&& iden >>> match false (checkSigWith (pks !! i) ih oh >>> true)

-- Vault --------------------------------------------------------------------------

-- | Withdraw: the input's internal key commits to a native template hash T
-- (key = tweak_embed_data(NUMS, T)), a relative delay has passed, and the
-- spending transaction matches T.  Recover: output 0 pays the recovery script.
vault :: (Simplicity term, Primitive term) => Word256 -> DW.Word16 -> Either Word256 () -> term () ()
vault recoverHash delay w = witness w &&& unit >>> match withdraw recover
 where
  withdraw = (keyOk &&& (delayOk &&& tplOk)) >>> unit
  keyOk = (unit >>> primitive Prim.InternalKey) &&& ((konst (w256 Ref.nums) &&& oh) >>> embedDataT) >>> eq >>> verify
  delayOk = unit >>> scribe (w16 (toInteger delay)) >>> TL.checkLockDistance
  tplOk = (unit >>> ctvNativeTemplate) &&& oh >>> eq >>> verify
  recover = (unit >>> scribe (w32 0) >>> primitive Prim.OutputScriptHash >>> verify) &&& konst recoverHash >>> eq >>> verify

-- DLC contract for difference -------------------------------------------------

-- | The oracle signs hash_DLC(event_id || price); output 0 receives
-- min(total, total * price / (2 * strike)) and output 1 the rest.
cfd :: (Simplicity term, Primitive term) => Word256 -> Word256 -> DW.Word64 -> DW.Word64 -> (Word64, SigW) -> term () ()
cfd oracle eventId total strike w = witness w >>> (sigOk &&& payoutOk) >>> unit
 where
  attestation = ((unit >>> ctx8InitTag "Simplicity/DLC/Attestation") &&& konst eventId >>> ctx8Add32) &&& oh >>> ctx8Add8 >>> ctx8Finalize
  sigOk = checkSigWith oracle attestation ih
  -- div2n1n (the DivMod128_64 jet) needs a normalized divisor (top bit set), so
  -- shift the 128-bit dividend and the constant divisor left by the divisor's leading zeros.
  divisor = 2 * toInteger strike
  k = length (takeWhile (< 2 ^ (63 :: Int)) (iterate (* 2) divisor))
  shiftedDividend = (konst (w64 (toInteger total)) &&& oh >>> Arith.multiply word64) >>> shift_const_by false word128 k
  long = (shiftedDividend &&& konst (w64 (divisor * 2 ^ k)) >>> Arith.div2n1n word64 >>> oh)
     &&& konst (w64 (toInteger total)) >>> Arith.min word64
  payoutOk = long >>> (out0 &&& out1) >>> unit
  out0 = iden &&& (unit >>> scribe (w32 0) >>> primitive Prim.OutputValue >>> verify) >>> eq >>> verify
  out1 = (konst (w64 (toInteger total)) &&& iden >>> Arith.subtract word64 >>> ih) &&& (unit >>> scribe (w32 1) >>> primitive Prim.OutputValue >>> verify) >>> eq >>> verify

cfdRef :: DW.Word64 -> DW.Word64 -> DW.Word64 -> DW.Word64
cfdRef total strike price = fromInteger (P.min (toInteger total) ((toInteger total * toInteger price) `div` (2 * toInteger strike)))

-- Merkle membership ------------------------------------------------------------

merkleDepth :: Int
merkleDepth = 16

-- | pk is a leaf of the depth-16 SHA-256 Merkle tree with root @root@, and pk signs sig_all_hash.
merkleKey :: (Simplicity term, Primitive term) => Word256 -> (Word256, (SigW, [(Bit, Word256)])) -> term () ()
merkleKey root (pk, (sig, path)) = (rootOk &&& sigOk) >>> unit
 where
  hashPair = (unit >>> ctx8Init) &&& iden >>> ctx8Add64 >>> ctx8Finalize
  -- level step: given the current node, combine with the witness sibling on the side given by the bit
  step (d, sib) = witness (d, sib) &&& iden >>> (ooh &&& (oih &&& ih)) >>> cond (hashPair) (ih &&& oh >>> hashPair)
  rootOk = witness pk >>> foldr (\x k -> step x >>> k) iden path >>> (iden &&& konst root) >>> eq >>> verify
  sigOk = (witness pk &&& sigMsg) &&& witness sig >>> Secp.bip_0340_verify

merkleRef :: BS.ByteString -> [(Bool, BS.ByteString)] -> BS.ByteString
merkleRef = L.foldl' (\cur (d, sib) -> hashToBytes (sha256 (if d then sib <> cur else cur <> sib)))

-- Vectors ----------------------------------------------------------------------

skA, skB, skC, skO :: Integer
skA = 0xB7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF
skB = 0xC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B14E5C9
skC = 0x0B432B2677937381AEF05BB02A66ECD012773062CF3FA2549E44F58ED2401710
skO = 0x0340034003400340034003400340034003400340034003400340034003400340

pkOf :: Integer -> Word256
pkOf = w256 . Ref.pubkeyOf

sigW :: Sig -> SigW
sigW (Sig r s) = (toWord256 (toInteger r), toWord256 (toInteger s))

simpleTx :: DW.Word32 -> DW.Word32 -> DW.Word32 -> [(DW.Word64, BS.ByteString)] -> SigTx
simpleTx ver lock sq outs = mkTx ver [mkInput (dummyOutpoint 0) 100000 (BSL.fromStrict (unhex "5120" <> BS.replicate 32 5)) sq] [ mkOutput v s | (v, s) <- outs ] lock

p2wpkh :: Int -> BS.ByteString
p2wpkh k = unhex "0014" <> BS.replicate 20 (fromIntegral k)

-- | Sign sig_all_hash for a program (given its CMR) in an environment.
signFor :: Integer -> Hash256 -> (Hash256 -> Maybe PrimEnv) -> SigW
signFor sk cmr env = maybe (error "signFor: env") (sigW . signMsg sk . sigMsgValue) (env cmr)

entries :: [Entry]
entries =
  [ Entry
    { entryId = "app-htlc"
    , entryTitle = "Hash time-locked contract (claim with preimage, refund after a height)"
    , entrySpec = "BOLT 3 offered-HTLC logic (SHA-256 payment hash, absolute timeout)"
    , entryCategory = BitcoinApp
    , entryVectorSource = Derived "preimage and signatures made with JetDiscovery.Ref.Bip340"
    , entryAssumptions = ["SHA-256 payment hash of a 32-byte preimage", "absolute block-height timeout"]
    , entryProgram = htlcProg
    , entryVectors =
        [ Vector "claim with preimage" (htlcEnv 100) (Left (w256FromBytes preimage, htlcSig skA 100)) Accept
        , Vector "claim with wrong preimage" (htlcEnv 100) (Left (w256 7, htlcSig skA 100)) Reject
        , Vector "refund after timeout" (htlcEnv 600) (Right (htlcSig skB 600)) Accept
        , Vector "refund before timeout" (htlcEnv 400) (Right (htlcSig skB 400)) Reject
        ]
    }
  , Entry
    { entryId = "app-multisig-2of3"
    , entryTitle = "2-of-3 BIP 340 multisig over sig_all_hash"
    , entrySpec = "k-of-n multisig (as OP_CHECKSIGADD in BIP 342)"
    , entryCategory = BitcoinApp
    , entryVectorSource = Derived "signatures made with JetDiscovery.Ref.Bip340"
    , entryAssumptions = ["three keys; each signature slot optional"]
    , entryProgram = msProg
    , entryVectors =
        [ Vector "A and B sign" msEnv [Just (msSig skA), Just (msSig skB), Nothing] Accept
        , Vector "B and C sign" msEnv [Nothing, Just (msSig skB), Just (msSig skC)] Accept
        , Vector "only A signs" msEnv [Just (msSig skA), Nothing, Nothing] Reject
        , Vector "C's signature in A's slot" msEnv [Just (msSig skC), Just (msSig skB), Nothing] Reject
        ]
    }
  , Entry
    { entryId = "app-vault"
    , entryTitle = "Vault: delayed withdrawal to a committed template, or immediate recovery"
    , entrySpec = "BIP 345 OP_VAULT use case, built from BIP 443-style data tweaks and a native template hash"
    , entryCategory = BitcoinApp
    , entryVectorSource = Derived "internal keys from Ref.embedData; template hashes from the native CTV reference"
    , entryAssumptions = [ "the withdrawal template is committed in the input's internal key (tweak_embed_data(NUMS, T))"
                         , "relative delay of " ++ show vaultDelay ++ " blocks; recovery output is output 0" ]
    , entryProgram = vaultProg
    , entryVectors =
        [ Vector "withdraw after the delay" (vaultEnv vaultDelay) (Left (vaultT vaultDelay)) Accept
        , Vector "withdraw before the delay" (vaultEnv (vaultDelay - 1)) (Left (vaultT (vaultDelay - 1))) Reject
        , Vector "withdraw to a different template" (vaultEnv vaultDelay) (Left (w256 99)) Reject
        , Vector "recover to the recovery script" recoverEnv (Right ()) Accept
        , Vector "recover to another script" (vaultEnv vaultDelay) (Right ()) Reject
        ]
    }
  , Entry
    { entryId = "app-dlc-cfd"
    , entryTitle = "Oracle-settled contract for difference (DLC-style, 64-bit payout arithmetic)"
    , entrySpec = "DLC numeric outcome settlement; exercises 64-bit arithmetic (as proposed for Script)"
    , entryCategory = BitcoinApp
    , entryVectorSource = Derived "oracle attestations made with JetDiscovery.Ref.Bip340; payouts from a Haskell reference"
    , entryAssumptions = [ "oracle signs hash_Simplicity/DLC/Attestation(event_id || price_be64)"
                         , "payout to output 0 is min(total, total * price / (2 * strike)); output 1 gets the rest" ]
    , entryProgram = cfdProg
    , entryVectors =
        [ Vector ("settle at price " ++ show p) (cfdEnv p) (w64 (toInteger p), attest p) Accept | p <- [30000, 50000, 70000, 150000] ] ++
        [ Vector "attestation for a different price" (cfdEnv 50000) (w64 50000, attest 50001) Reject
        , Vector "payout does not match the price" (cfdEnvRaw 50000 (cfdRef cfdTotal cfdStrike 50000 + 1)) (w64 50000, attest 50000) Reject ]
    }
  , Entry
    { entryId = "app-merkle-key"
    , entryTitle = "Merkle tree of keys (depth 16): prove membership, then sign"
    , entrySpec = "BIP 347 motivation: tree signatures (Merkle paths built with OP_CAT + OP_SHA256)"
    , entryCategory = BitcoinApp
    , entryVectorSource = Derived "Merkle roots from a Haskell reference"
    , entryAssumptions = ["fixed depth 16 (65536 leaves); leaf = x-only public key; SHA-256 of the 64-byte concatenation"]
    , entryProgram = mkProg
    , entryVectors =
        [ Vector "member signs" mkEnv' (mkW skA mkPath) Accept
        , Vector "wrong sibling" mkEnv' (mkW skA (let ((d, _):r) = mkPath in (d, BS.replicate 32 0) : r)) Reject
        , Vector "non-member key" mkEnv' (mkW skB mkPath) Reject
        ]
    }
  ]
 where
  -- HTLC
  preimage = BS.replicate 32 0x42
  hashH = w256FromBytes (hashToBytes (sha256 preimage))
  htlcTimeout = 500
  htlcProg w = Prog (htlc hashH (pkOf skA) (pkOf skB) htlcTimeout w)
  htlcCmr = progCmr (htlcProg (Right (w256 0, w256 0)))
  htlcEnv lock = mkEnv (simpleTx 2 lock 0xfffffffe [(99000, p2wpkh 1)]) 0 defaultTap
  htlcSig sk lock = signFor sk htlcCmr (htlcEnv lock)
  -- multisig
  msProg sigs = Prog (multisig2of3 (map pkOf [skA, skB, skC]) sigs)
  msCmr = progCmr (msProg [Nothing, Nothing, Nothing])
  msEnv = mkEnv (simpleTx 2 0 0xfffffffd [(99000, p2wpkh 2)]) 0 defaultTap
  msSig sk = signFor sk msCmr msEnv
  -- vault
  vaultDelay = 144 :: DW.Word16
  recoveryScript = p2wpkh 9
  vaultProg w = Prog (vault (w256FromBytes (hashToBytes (sha256 recoveryScript))) vaultDelay w)
  vaultTx d = simpleTx 2 0 (fromIntegral d) [(99000, p2wpkh 3)]
  vaultT d = w256FromBytes (hashToBytes (ctvNativeRef (vaultTx d) 0))
  vaultTap d c = (defaultTap c) { tapInternalKey = PubKey (fromInteger (Ref.embedData Ref.nums (w256ToBytes (vaultT d)))) }
  vaultEnv d = mkEnv (vaultTx d) 0 (vaultTap d)
  recoverEnv = mkEnv (simpleTx 2 0 0xffffffff [(99000, recoveryScript)]) 0 defaultTap
  -- CFD
  cfdTotal = 1000000 :: DW.Word64
  cfdStrike = 50000 :: DW.Word64
  eventId = BS.replicate 32 0xee
  cfdProg w = Prog (cfd (pkOf skO) (w256FromBytes eventId) cfdTotal cfdStrike w)
  attestMsg p = hashToBytes (taggedSha256 "Simplicity/DLC/Attestation" (eventId <> runPut (putWord64be p)))
  attest p = sigW (signMsg skO (attestMsg p))
  cfdEnvRaw p long = mkEnv (simpleTx 2 0 0xffffffff [(long, p2wpkh 4), (cfdTotal - long, p2wpkh 5)]) 0 defaultTap
  cfdEnv p = cfdEnvRaw p (cfdRef cfdTotal cfdStrike p)
  -- Merkle
  mkPath = [ (odd i, BS.replicate 32 (fromIntegral i)) | i <- [1 .. merkleDepth] ]
  mkRoot = merkleRef (Ref.bytesFromInt (Ref.pubkeyOf skA)) mkPath
  mkProg w = Prog (merkleKey (w256FromBytes mkRoot) w)
  mkCmr = progCmr (mkProg (w256 0, ((w256 0, w256 0), [ (false', w256 0) | _ <- mkPath ])))
  false' = Left () :: Bit
  mkEnv' = mkEnv (simpleTx 2 0 0xffffffff [(99000, p2wpkh 6)]) 0 defaultTap
  mkW sk path = (pkOf sk, (signFor sk mkCmr mkEnv', [ (if d then Right () else Left (), w256FromBytes s) | (d, s) <- path ]))
