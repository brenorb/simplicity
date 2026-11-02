-- | BIP 119 OP_CHECKTEMPLATEVERIFY.
--
-- * @bip119-ctv-exact@ computes BIP 119's DefaultCheckTemplateVerifyHash
--   bit-for-bit.  BIP 119 hashes serialized output scripts and scriptSigs, but
--   Bitcoin Simplicity only exposes their SHA-256 hashes
--   (@output_script_hash@, @input_script_sig_hash@).  So the program takes the
--   raw bytes as witness data, checks them against the hashes, and
--   re-serializes them.  Loops are unrolled to fixed bounds.
--
-- * @bip119-ctv-native@ commits to the same transaction fields using the
--   existing Simplicity hash jets (@outputs_hash@, @input_sequences_hash@, ...).
--   It is not hash-compatible with BIP 119, but it gives a covenant of the
--   same strength.
module JetDiscovery.Corpus.Bip119Ctv
  ( entries
  , maxIns, maxOuts
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.List as L
import qualified Data.Vector as V
import Data.Serialize (runPutLazy, putWord32be, put)
import qualified Data.Word as DW

import Simplicity.Digest (Hash256, bslHash)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (scribe, eq)
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import Simplicity.Bitcoin.DataTypes
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types

maxIns, maxOuts :: Int
maxIns = 16
maxOuts = 16

-- | Thread a SHA-256 context through @t@: @ctxWith t step@ appends @t@'s output with @step@.
ctxWith :: (Core term, TyC x) => term () x -> term (Ctx8, x) Ctx8 -> term Ctx8 Ctx8
ctxWith t step = iden &&& (unit >>> t) >>> step

-- | Process output @i@ given its script bytes as witness: check the script
-- hash and append @value_le64 || ser_string(script)@.
outStep :: (Assert term, Primitive term, Witness term) => Int -> Buffer511 Word8 -> term Ctx8 Ctx8
outStep i script = (unit >>> scribe (w32 (toInteger i)) >>> primitive Prim.OutputValue) &&& iden >>> match ih present
 where
  -- input (Word64 value, Ctx8)
  present = (unit >>> witness script) &&& iden >>> checked
  -- input (Buffer511, (Word64, Ctx8))
  checked = (take sha256Buffer511 &&& (unit >>> scribe (w32 (toInteger i)) >>> primitive Prim.OutputScriptHash >>> verify) >>> eq >>> verify)
        &&& ((drop (ih &&& oh >>> ctxAddLE64)) &&& oh >>> ctxAddVarString511)
        >>> ih

-- | Process input @i@: append its LE sequence number to the sequences context.
seqStep :: (Assert term, Primitive term) => Int -> term Ctx8 Ctx8
seqStep i = (unit >>> scribe (w32 (toInteger i)) >>> primitive Prim.InputSequence) &&& iden >>> match ih (ih &&& oh >>> ctxAddLE32)

-- | Process input @i@'s scriptSig (witness bytes): check its hash, append
-- @ser_string(scriptSig)@, and record whether it is non-empty.
-- State: (any non-empty so far, context).
ssStep :: (Assert term, Primitive term, Witness term) => Int -> Buffer511 Word8 -> term (Bit, Ctx8) (Bit, Ctx8)
ssStep i ss = (unit >>> scribe (w32 (toInteger i)) >>> primitive Prim.InputScriptSigHash) &&& iden >>> match ih present
 where
  -- input (Word256 expected hash, (Bit, Ctx8))
  present = (unit >>> witness ss) &&& iden >>> checked
  -- input (Buffer511, (Word256, (Bit, Ctx8)))
  checked = (take sha256Buffer511 &&& ioh >>> eq >>> verify)
        &&& ((take nonEmpty &&& iioh >>> or oh ih) &&& (iiih &&& oh >>> ctxAddVarString511))
        >>> ih
  nonEmpty = buf511Len >>> some16
  some16 = iden &&& scribe (w16 0) >>> eq >>> not iden

-- | DefaultCheckTemplateVerifyHash of the current input, compared to @h@.
ctvExact :: (Assert term, Primitive term, Witness term) => Word256 -> [Buffer511 Word8] -> [Buffer511 Word8] -> term () ()
ctvExact h scriptSigs scripts = (template &&& witness h >>> eq >>> verify)
 where
  ssState = (false &&& ctx8Init) >>> foldr (\(i, s) k -> ssStep i s >>> k) iden (zip [0 ..] scriptSigs)
  seqHash = ctx8Init >>> foldr (\i k -> seqStep i >>> k) iden [0 .. maxIns - 1] >>> ctx8Finalize
  outHash = ctx8Init >>> foldr (\(i, s) k -> outStep i s >>> k) iden (zip [0 ..] scripts) >>> ctx8Finalize
  -- if any scriptSig is non-empty, append sha256(serialized scriptSigs)
  addSS = iden &&& (unit >>> ssState) >>> (ioh &&& (oh &&& drop (drop ctx8Finalize))) >>> cond (ctx8Add32) oh
  template = ctx8Init
         >>> ctxWith (primitive Prim.Version) ctxAddLE32
         >>> ctxWith (primitive Prim.LockTime) ctxAddLE32
         >>> addSS
         >>> ctxWith Tx.numInputs ctxAddLE32
         >>> ctxWith seqHash ctx8Add32
         >>> ctxWith Tx.numOutputs ctxAddLE32
         >>> ctxWith outHash ctx8Add32
         >>> ctxWith (primitive Prim.CurrentIndex) ctxAddLE32
         >>> ctx8Finalize

-- | A Simplicity-native template hash over the same fields, using existing hash jets.
ctvNative :: (Assert term, Primitive term, Witness term) => Word256 -> term () ()
ctvNative h = (template &&& witness h >>> eq >>> verify)
 where
  template = ctx8Init
         >>> ctxWith (primitive Prim.Version) ctx8Add4
         >>> ctxWith (primitive Prim.LockTime) ctx8Add4
         >>> ctxWith SigHash.inputScriptSigsHash ctx8Add32
         >>> ctxWith Tx.numInputs ctx8Add4
         >>> ctxWith SigHash.inputSequencesHash ctx8Add32
         >>> ctxWith Tx.numOutputs ctx8Add4
         >>> ctxWith SigHash.outputsHash ctx8Add32
         >>> ctxWith (primitive Prim.CurrentIndex) ctx8Add4
         >>> ctx8Finalize

-- | Haskell reference for 'ctvNative' (independent of the jets: uses Simplicity.Bitcoin.DataTypes).
ctvNativeRef :: SigTx -> DW.Word32 -> Hash256
ctvNativeRef tx ix = bslHash . runPutLazy $ do
  putWord32be (sigTxVersion tx)
  putWord32be (sigTxLock tx)
  put (inputScriptSigsHash tx)
  putWord32be (fromIntegral (V.length (sigTxIn tx)))
  put (inputSequencesHash tx)
  putWord32be (fromIntegral (V.length (sigTxOut tx)))
  put (outputsHash tx)
  putWord32be ix

data CtvVec = CtvVec { cvTxNo :: Int, cvTx :: RawTx, cvIx :: DW.Word32, cvHash :: BS.ByteString }

loadVectors :: IO [CtvVec]
loadVectors = do
  s <- readFile "vendor-specs/bips/bip-0119_vectors_ctvhash.json"
  return [ CtvVec n tx ix (unhex h)
         | (n, (txHex, ixs, hs)) <- zip [0 ..] (parseCtvJson s)
         , Right tx <- [parseRawTx (unhex txHex)]
         , (ix, h) <- zip ixs hs
         , fromIntegral ix < length (rtIns tx) ]

-- | Minimal parser for ctvhash.json: objects with "hex_tx", "spend_index" and "result".
parseCtvJson :: String -> [(String, [DW.Word32], [String])]
parseCtvJson s = go s
 where
  go str = case breakOn "\"hex_tx\"" str of
    Nothing -> []
    Just rest -> let (txHex, r1) = strField rest
                     Just r2 = breakOn "\"spend_index\"" r1
                     (ixs, r3) = listField r2
                     Just r4 = breakOn "\"result\"" r3
                     (res, r5) = listField r4
                 in if null txHex || txHex == "string (hex tx)" then go r5 else (txHex, map read ixs, map (filter (/= '"')) res) : go r5
  breakOn pat str | pat `L.isPrefixOf` str = Just (L.drop (length pat) str)
                  | null str = Nothing
                  | otherwise = breakOn pat (tail str)
  strField str = let a = L.drop 1 (L.dropWhile (/= '"') (L.drop 1 (L.dropWhile (/= ':') str)))
                 in (L.takeWhile (/= '"') a, L.drop 1 (L.dropWhile (/= '"') a))
  listField str = let a = L.drop 1 (L.dropWhile (/= '[') str)
                      (inside, rest) = break (== ']') a
                  in (filter (\x -> x /= "") (map (filter (`notElem` " \n\t")) (splitC inside)), L.drop 1 rest)
  splitC xs = case break (== ',') xs of
    (a, []) -> [a]
    (a, _:r) -> a : splitC r

-- | Witness for the exact program: (template hash, scriptSigs, output scripts), padded to the bounds.
type ExactW = (Word256, ([Buffer511 Word8], [Buffer511 Word8]))

exactWitness :: CtvVec -> ExactW
exactWitness v = (w256FromBytes (cvHash v), (pad maxIns (map riScriptSig (rtIns (cvTx v))), pad maxOuts (map roScript (rtOuts (cvTx v)))))
 where pad n xs = map buffer511FromBytes (L.take n (xs ++ repeat BS.empty))

fits :: CtvVec -> Bool
fits v = length (rtIns tx) <= maxIns && length (rtOuts tx) <= maxOuts
      && all ((<= 511) . BS.length . riScriptSig) (rtIns tx) && all ((<= 511) . BS.length . roScript) (rtOuts tx)
 where tx = cvTx v

entries :: IO [Entry]
entries = do
  vs <- filter fits <$> loadVectors
  -- One spend index per transaction keeps the run time reasonable; 100 transactions.
  let firstPerTx = L.nubBy (\a b -> cvTxNo a == cvTxNo b) vs
      envOf v = mkEnv (rawToSigTx (cvTx v)) (cvIx v) defaultTap
      flipBit w = w256FromBytes (BS.pack (let (b:bs) = BS.unpack (w256ToBytes w) in (b + 1) : bs))
      exactVec v = Vector ("ctvhash.json tx with " ++ show (length (rtIns (cvTx v))) ++ " inputs, " ++ show (length (rtOuts (cvTx v))) ++ " outputs, index " ++ show (cvIx v))
                          (envOf v) (exactWitness v) Accept
      badHash v = let (h, r) = exactWitness v in Vector "wrong template hash" (envOf v) (flipBit h, r) Reject
      badScript v = let (h, (ss, scs)) = exactWitness v
                        scs' = case scs of (_:rest) -> buffer511FromBytes (BS.pack [0x51]) : rest; [] -> []
                    in Vector "output script bytes that do not match output_script_hash" (envOf v) (h, (ss, scs')) Reject
      nativeVec v = let tx = rawToSigTx (cvTx v)
                    in Vector ("native template of ctvhash.json tx, index " ++ show (cvIx v)) (envOf v)
                              (w256FromBytes (hashToBytes (ctvNativeRef tx (cvIx v)))) Accept
      nativeBad v = let tx = rawToSigTx (cvTx v)
                    in Vector "native template for a different input index" (envOf v)
                              (w256FromBytes (hashToBytes (ctvNativeRef tx (cvIx v + 1)))) Reject
  return
    [ Entry
      { entryId = "bip119-ctv-exact"
      , entryTitle = "OP_CHECKTEMPLATEVERIFY, bit-for-bit BIP 119 template hash"
      , entrySpec = "BIP 119 DefaultCheckTemplateVerifyHash (vendor-specs/bips/bip-0119.mediawiki)"
      , entryCategory = CovenantBip
      , entryVectorSource = Upstream ("vendor-specs/bips/bip-0119_vectors_ctvhash.json: " ++ show (length firstPerTx)
                                       ++ " transactions (first in-range spend index each), plus 2 negative vectors")
      , entryAssumptions = [ "at most " ++ show maxIns ++ " inputs and " ++ show maxOuts ++ " outputs (loops unrolled to these bounds)"
                           , "output scripts and scriptSigs of at most 511 bytes, supplied as witness bytes"
                           , "the template hash is a witness operand (in a real covenant it is a constant)"
                           , "ctvhash.json spend indices beyond the input count are skipped: Simplicity's current_index is always a real input" ]
      , entryProgram = \(h, (ss, scs)) -> Prog (ctvExact h ss scs)
      , entryVectors = map exactVec firstPerTx ++ [badHash (head firstPerTx), badScript (head firstPerTx)]
      }
    , Entry
      { entryId = "bip119-ctv-native"
      , entryTitle = "CTV-equivalent covenant using Simplicity's native transaction hashes"
      , entrySpec = "BIP 119 semantics with Simplicity hash jets (not hash-compatible with BIP 119)"
      , entryCategory = CovenantBip
      , entryVectorSource = Derived "transactions from bip-0119_vectors_ctvhash.json; expected hashes from a Haskell reference over Simplicity.Bitcoin.DataTypes"
      , entryAssumptions = ["the template hash is a witness operand (in a real covenant it is a constant)"]
      , entryProgram = \h -> Prog (ctvNative h)
      , entryVectors = map nativeVec firstPerTx ++ [nativeBad (head firstPerTx)]
      }
    ]
