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

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (scribe, eq)
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.DataTypes
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer
import JetDiscovery.Tx
import JetDiscovery.Types

-- | hash_TemplateHash(nVersion || nLockTime || sha_sequences || sha_outputs || annex_present || input_index [|| sha_annex]) == h
templateHash :: (Assert term, Primitive term, Witness term) => Word256 -> [Buffer511 Word8] -> Buffer511 Word8 -> term () ()
templateHash h scripts annex = template &&& witness h >>> eq >>> verify
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
  withAnnex = (((unit >>> witness annex >>> sha256Buffer511) &&& oh >>> eq >>> verify) &&& ih) >>> ih
          >>> ctxWith (scribe (w8 1)) ctx8Add1 >>> addIndex
          >>> ctxWith ((ctx8Init &&& witness annex) >>> ctxAddVarString511 >>> ctx8Finalize) ctx8Add32

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

entries :: IO [Entry]
entries = do
  vs <- loadVectors
  let pad n xs = map buffer511FromBytes (L.take n (xs ++ repeat BS.empty))
      vec v = Vector ("basics.json: " ++ tvComment v) (mkEnv (tvTx v) (fromIntegral (tvIx v)) defaultTap)
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
    ]
