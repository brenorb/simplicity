-- | BIP 446 OP_TEMPLATEHASH: the taproot-native successor of CTV.
--
-- The template hash reuses BIP 341's @sha_sequences@, @sha_outputs@ and
-- @sha_annex@.  Bitcoin Simplicity exposes neither raw output scripts nor a
-- BIP 341 compatible annex hash (its annex hash omits the CompactSize prefix),
-- so, as for exact CTV, the scripts and the annex are witness bytes checked
-- against the hash primitives and then re-serialized.
module JetDiscovery.Corpus.Bip446TemplateHash
  ( entries
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.List as L
import qualified Data.Vector as V
import qualified Data.Word as DW
import Simplicity.Digest (Hash256)
import Simplicity.Bitcoin.Primitive (PrimEnv)

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (scribe, eq)
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.DataTypes
import Simplicity.Ty.Word
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.LibSecp256k1.Schnorr (PubKey(..), Sig(..))
import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Run (progCmr)
import qualified JetDiscovery.Ref.Bip340 as Ref

import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer
import JetDiscovery.Tx
import JetDiscovery.Types

-- | hash_TemplateHash(nVersion || nLockTime || sha_sequences || sha_outputs || annex_present || input_index [|| sha_annex]) == h
templateHash :: (Assert term, Primitive term, Witness term) => Word256 -> [Buffer511 Word8] -> Buffer511 Word8 -> term () ()
templateHash h scripts annex = templateTerm scripts annex &&& witness h >>> eq >>> verify

-- | BIP 448 LN-Symmetry update: OP_TEMPLATEHASH OP_INTERNALKEY OP_CHECKSIGFROMSTACK, i.e. a
-- signature by the taproot internal key on the template hash (rebindable to any prevout).
lnSymmetryUpdate :: (Assert term, Primitive term, Witness term) => [Buffer511 Word8] -> Buffer511 Word8 -> (Word256, Word256) -> term () ()
lnSymmetryUpdate scripts annex sig = ((primitive Prim.InternalKey &&& templateTerm scripts annex) &&& witness sig) >>> Secp.bip_0340_verify

-- | The BIP 446 template hash of the current input's transaction.
templateTerm :: (Assert term, Primitive term, Witness term) => [Buffer511 Word8] -> Buffer511 Word8 -> term () Word256
templateTerm scripts annex = template
 where
  template = ctx8InitTag "TemplateHash"
         >>> ctxWith (primitive Prim.Version) ctxAddLE32
         >>> ctxWith (primitive Prim.LockTime) ctxAddLE32
         >>> ctxWith shaSequences ctx8Add32
         >>> ctxWith (shaOutputs scripts) ctx8Add32
         >>> ((unit >>> Tx.currentAnnexHash) &&& iden >>> match noAnnex withAnnex)
         >>> ctx8Finalize
  addIndex = ctxWith (primitive Prim.CurrentIndex) ctxAddLE32
  noAnnex = ih >>> ctxWith (scribe (w8 0)) ctx8Add1 >>> addIndex
  -- input (Word256 annex hash as Simplicity defines it: sha256(annex), Ctx8)
  -- Bind the annex once. The raw-hash check and BIP341 reserialization
  -- must use projections of that same input, not copied witness nodes.
  withAnnex = (witness annex &&& iden) >>> (rawHashOk &&& appendAnnex) >>> ih
  rawHashOk = (take sha256Buffer511 &&& ioh) >>> eq >>> verify
  baseContext = iih >>> ctxWith (scribe (w8 1)) ctx8Add1 >>> addIndex
  bipAnnexHash = ((unit >>> ctx8Init) &&& oh) >>> ctxAddVarString511 >>> ctx8Finalize
  appendAnnex = (baseContext &&& bipAnnexHash) >>> ctx8Add32

data TVec = TVec { tvTx :: SigTx, tvIx :: Int, tvHash :: BS.ByteString, tvScripts :: [BS.ByteString], tvAnnex :: BS.ByteString
                 , tvValid :: Bool, tvComment :: String }

-- | Build the 'SigTx' for a basics.json case: spent outputs supply input values and scripts; annexes come from the witnesses.
toSigTx :: RawTx -> [TxOutput] -> SigTx
toSigTx raw spent = (rawToSigTx raw) { sigTxIn = V.fromList (zipWith3 inp (rtIns raw) spent (rtWitness raw)) }
 where
  inp (RawIn op ss sq) txo wit = SigTxInput op txo sq (BSL.fromStrict <$> taprootAnnex wit) (BSL.fromStrict ss)

loadVectors :: IO [TVec]
loadVectors = do
  s <- readFile "vendor-specs/bips/bip-0446_basics.json"
  return (map mk (objects s))
 where
  mk o = let Right raw = parseRawTx (unhex (field "spending_tx" o))
             spent = [ t | Right t <- map (parseTxOut . unhex) (arrayField "spent_outputs" o) ]
             ix = read (rawField "input_index" o)
             stack = rtWitness raw !! ix
             annex = taprootAnnex stack
             script = stack !! (length stack - (if annex == Nothing then 2 else 3))
             h = BS.take 32 (BS.drop 1 script)  -- script is <push 32 bytes> OP_TEMPLATEHASH OP_EQUAL
         in TVec (toSigTx raw spent) ix h (map roScript (rtOuts raw)) (maybe BS.empty id annex)
                 (rawField "valid" o == "true") (field "comment" o)
  -- A tiny JSON reader for this file's flat objects.
  objects str = case L.dropWhile (/= '{') str of
    [] -> []
    (_:r) -> let (o, rest) = break (== '}') r in o : objects rest
  key k o = case L.findIndex (L.isPrefixOf ("\"" ++ k ++ "\"")) (L.tails o) of
    Just i -> L.drop 1 (L.dropWhile (/= ':') (L.drop i o))
    Nothing -> error ("missing key " ++ k)
  field k o = L.takeWhile (/= '"') (L.drop 1 (L.dropWhile (/= '"') (key k o)))
  rawField k o = L.takeWhile (`notElem` ",}\n ") (L.dropWhile (== ' ') (key k o))
  arrayField k o = let inside = L.takeWhile (/= ']') (L.drop 1 (L.dropWhile (/= '[') (key k o)))
                   in [ L.takeWhile (/= '"') x | x <- map (L.drop 1 . L.dropWhile (/= '"')) (splitC inside), x /= "" ]
  splitC xs = case break (== ',') xs of
    (a, []) -> [a]
    (a, _:r) -> a : splitC r

pad :: Int -> [BS.ByteString] -> [Buffer511 Word8]
pad n xs = map buffer511FromBytes (L.take n (xs ++ repeat BS.empty))

lsSk :: Integer
lsSk = 0xC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B14E5C9

lsScript :: BS.ByteString
lsScript = unhex "5120" <> BS.replicate 32 0x3c

lsEnv :: Outpoint -> DW.Word64 -> Hash256 -> Maybe PrimEnv
lsEnv op v = mkEnv (mkTx 2 [mkInput op 100000 mempty 0xfffffffd] [mkOutput v lsScript] 0) 0
                   (\c -> (defaultTap c) { tapInternalKey = PubKey (fromInteger (Ref.pubkeyOf lsSk)) })

lsSig :: (Word256, Word256)
lsSig = case lsEnv (dummyOutpoint 0) 90000 cmr >>= \e -> Jets.fastEval (templateTerm (pad maxOuts [lsScript]) (buffer511FromBytes BS.empty)) e () of
  Just h -> let Sig r s = signMsg lsSk (w256ToBytes h) in (toWord256 (toInteger r), toWord256 (toInteger s))
  Nothing -> error "lsSig"
 where cmr = progCmr (Prog (lnSymmetryUpdate (pad maxOuts [lsScript]) (buffer511FromBytes BS.empty) (toWord256 0, toWord256 0)))

entries :: IO [Entry]
entries = do
  vs <- loadVectors
  let vec v = Vector ("basics.json: " ++ tvComment v) (mkEnv (tvTx v) (fromIntegral (tvIx v)) defaultTap)
                     (w256FromBytes (tvHash v), (pad maxOuts (tvScripts v), buffer511FromBytes (tvAnnex v)))
                     (if tvValid v then Accept else Reject)
  return
    [ Entry
      { entryId = "bip446-templatehash-exact"
      , entryTitle = "OP_TEMPLATEHASH, bit-for-bit BIP 446 template hash"
      , entrySpec = "BIP 446 (vendor-specs/bips/bip-0446.md)"
      , entryCategory = CovenantBip
      , entryVectorSource = Upstream "vendor-specs/bips/bip-0446_basics.json (all 19 cases; expected hash read from each spending tapscript)"
      , entryAssumptions = [ "at most " ++ show maxIns ++ " inputs and " ++ show maxOuts ++ " outputs"
                           , "output scripts and the annex are at most 511 bytes and supplied as witness bytes"
                           , "the committed hash is a witness operand (in a real script it is a constant)" ]
      , entryProgram = \(h, (scs, annex)) -> Prog (templateHash h scs annex)
      , entryVectors = map vec vs
      }
    , Entry
      { entryId = "bip448-lnsymmetry-update"
      , entryTitle = "LN-Symmetry update spend: internal-key signature on the BIP 446 template hash"
      , entrySpec = "BIP 448 (vendor-specs/bips/bip-0448.md): OP_TEMPLATEHASH + OP_CHECKSIGFROMSTACK + OP_INTERNALKEY"
      , entryCategory = CovenantBip
      , entryVectorSource = Derived "BIP 340 signatures on the template hash evaluated in each environment"
      , entryAssumptions = [ "single output, no annex; output scripts are witness bytes as for bip446-templatehash-exact" ]
      , entryProgram = \(scs, sig) -> Prog (lnSymmetryUpdate (pad maxOuts scs) (buffer511FromBytes BS.empty) sig)
      , entryVectors =
          [ Vector "update signed by the channel key" (lsEnv (dummyOutpoint 0) 90000) ([lsScript], lsSig) Accept
          , Vector "same signature rebinds to another channel state's outpoint" (lsEnv (Outpoint (hashFromInteger 0xfeed) 1) 90000) ([lsScript], lsSig) Accept
          , Vector "different settlement output" (lsEnv (dummyOutpoint 0) 80000) ([lsScript], lsSig) Reject
          ]
      }
    ]
