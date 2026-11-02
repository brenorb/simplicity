-- | BIP 348 OP_CHECKSIGFROMSTACK: verify a BIP 340 signature on an arbitrary
-- message taken from the witness.
--
-- Two programs:
--
-- * @bip348-csfs@: messages of 0 to 511 bytes.  The BIP 340 challenge hash is
--   computed with the SHA-256 context jets over a witness buffer, and the
--   curve check uses the @point_verify_1@ jet.  The existing @bip_0340_verify@
--   jet only accepts 32-byte messages.
-- * @bip348-csfs-32@: the 32-byte-message special case, using @bip_0340_verify@.
--
-- Operands (public key, message, signature) are all witness data, so the
-- program measures exactly the opcode's work.
module JetDiscovery.Corpus.Bip348Csfs
  ( entries
  , csfsVarLen
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.List as L

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types

-- | Variable length BIP 340 verification: input ((pubkey, message), (r, s)).
csfsVarLen :: Assert term => term ((Word256, Buffer511 Word8), (Word256, Word256)) ()
csfsVarLen = take (take Secp.pubkey_unpack_neg) &&& (challenge &&& drop Secp.signature_unpack) >>> match failure k1
 where
  -- e = int(tagged_hash("BIP0340/challenge", r || P || m)) mod n
  challenge = ((((unit >>> ctx8InitTag "BIP0340/challenge") &&& drop oh >>> ctx8Add32) &&& ooh >>> ctx8Add32) &&& oih >>> ctx8AddBuffer511)
          >>> ctx8Finalize >>> Secp.scalar_normalize
  k1 = iih &&& (ioh &&& oh) >>> match failure k2
  k2 = (ih &&& oih) &&& ((unit >>> false) &&& ooh) >>> Secp.point_verify_1

csfs32 :: Assert term => term ((Word256, Word256), (Word256, Word256)) ()
csfs32 = Secp.bip_0340_verify

data Row = Row { rIndex :: String, rPk :: BS.ByteString, rMsg :: BS.ByteString, rSig :: BS.ByteString, rOk :: Bool, rComment :: String }

parseCsv :: String -> [Row]
parseCsv = map row . L.drop 1 . lines
 where
  row l = case splitOn ',' l of
    (i:_sk:pk:_aux:msg:sig:res:rest) -> Row i (unhex pk) (unhex msg) (unhex sig) (res == "TRUE") (concat rest)
    _ -> error ("bad csv row: " ++ l)
  splitOn c s = case break (== c) s of
    (a, []) -> [a]
    (a, _:r) -> a : splitOn c r

entries :: IO [Entry]
entries = do
  rows <- parseCsv <$> readFile "vendor-specs/bips/bip-0340_test-vectors.csv"
  let env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
      vec r w = Vector ("BIP340 vector " ++ rIndex r ++ (if null (rComment r) then "" else " (" ++ rComment r ++ ")"))
                       env w (if rOk r then Accept else Reject)
      sig r = (w256FromBytes (BS.take 32 (rSig r)), w256FromBytes (BS.drop 32 (rSig r)))
  return
    [ Entry
      { entryId = "bip348-csfs"
      , entryTitle = "OP_CHECKSIGFROMSTACK with 0-511 byte messages"
      , entrySpec = "BIP 348 (vendor-specs/bips/bip-0348.md), signature rules of BIP 340"
      , entryCategory = CovenantBip
      , entryVectorSource = Upstream "vendor-specs/bips/bip-0340_test-vectors.csv (all 19 rows)"
      , entryAssumptions = [ "public key, message and signature are witness operands"
                           , "messages up to 511 bytes (BIP 348 allows up to the 520-byte stack element limit)"
                           , "only 32-byte public keys (unknown key types are a Script upgrade hook, not modelled)" ]
      , entryProgram = \((pk, msg), s) -> Prog (witness ((w256FromBytes pk, buffer511FromBytes msg), s) >>> csfsVarLen)
      , entryVectors = [ vec r ((rPk r, rMsg r), sig r) | r <- rows ]
      }
    , Entry
      { entryId = "bip348-csfs-32"
      , entryTitle = "OP_CHECKSIGFROMSTACK restricted to 32-byte messages (existing bip_0340_verify jet)"
      , entrySpec = "BIP 348 with 32-byte messages"
      , entryCategory = CovenantBip
      , entryVectorSource = Upstream "vendor-specs/bips/bip-0340_test-vectors.csv (rows with 32-byte messages)"
      , entryAssumptions = ["public key, message and signature are witness operands", "message is exactly 32 bytes"]
      , entryProgram = \((pk, msg), s) -> Prog (witness ((w256FromBytes pk, w256FromBytes msg), s) >>> csfs32)
      , entryVectors = [ vec r ((rPk r, rMsg r), sig r) | r <- rows, BS.length (rMsg r) == 32 ]
      }
    ]
