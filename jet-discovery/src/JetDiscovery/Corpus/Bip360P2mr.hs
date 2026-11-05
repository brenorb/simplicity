-- | P2MR output construction with every successful upstream leaf opening.
-- This checks the output commitment; it does not interpret a Tapscript leaf.
module JetDiscovery.Corpus.Bip360P2mr (entries) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import qualified Data.List as L

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.Bitcoin.Lib as BLib
import Simplicity.Bitcoin.Term (Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types

maxDepth :: Int
maxDepth = 8

type Opening = (Integer, BS.ByteString, [Maybe BS.ByteString])

p2mr :: (Assert term, Primitive term, Witness term) => Opening -> term () ()
p2mr (version, script, path) = outputHash &&& actual >>> eq >>> verify
 where
  leaf = ((ctx8InitTag "TapLeaf" &&& witness (w8 version) >>> ctx8Add1)
       &&& witness (buffer511FromBytes script)) >>> ctxAddVarString511 >>> ctx8Finalize
  step sibling = witness (maybe (Left ()) (Right . w256FromBytes) sibling) &&& iden
              >>> match ih BLib.buildTapbranch
  root = leaf >>> foldr (\s k -> step s >>> k) iden path
  outputHash = ((ctx8Init &&& konst (w16 0x5220) >>> ctx8Add2) &&& root) >>> ctx8Add32 >>> ctx8Finalize
  actual = konst (w32 0) >>> primitive Prim.OutputScriptHash >>> verify

entries :: IO [Entry]
entries = do
  contents <- readFile "corpus/bips/bip360-leaf-openings.tsv"
  let records = map parse (tail (lines contents))
      parse line = case split '\t' line of
        [source, name, leafIx, ver, script, path, spk] ->
          let siblings = if null path then [] else map unhex (split ',' path)
          in if length siblings > maxDepth || BS.length (unhex script) > 511
             then error "BIP360 vector exceeds declared Simplicity bounds"
             else (source ++ ":" ++ name ++ ":" ++ leafIx,
                   (read ver, unhex script, L.take maxDepth (map Just siblings ++ repeat Nothing)), unhex spk)
        _ -> error "malformed BIP360 TSV row; regenerate with tools/extract_bip360_vectors.py"
      env script = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 script] 0) 0 defaultTap
      positive = [Vector name (env spk) opening Accept | (name, opening, spk) <- records]
      (name0, opening0@(version0, script0, path0), spk0) = head records
      negatives =
        [ Vector "derived wrong leaf script" (env spk0) (version0, script0 <> BS.singleton 0, path0) Reject
        , Vector "derived wrong leaf version" (env spk0) (version0 + 2, script0, path0) Reject
        , Vector "derived P2TR output instead of P2MR" (env (BS.pack [0x51,0x20] <> BS.drop 2 spk0)) opening0 Reject ]
  return [Entry
    { entryId = "bip360-upstream-p2mr-output"
    , entryTitle = "P2MR output: arbitrary published leaf script and Merkle opening"
    , entrySpec = "BIP360 at a0c977f3755da6476b955677ca9318334a2432c4; both upstream p2mr*_construction.json files"
    , entryCategory = CovenantBip
    , entryVectorSource = Upstream "all 29 leaf openings from all 13 successful construction cases; TSV is derived by tools/extract_bip360_vectors.py, which also checks all 3 constructor rejection cases; plus 3 derived negative spend vectors"
    , entryAssumptions = ["leaf script at most 511 bytes; Merkle path at most 8 levels; version, script and path are witness data"
                         ,"checks output construction only: wallet address encoding, P2MR activation and execution of the enclosed Tapscript are outside the program"]
    , entryProgram = \opening -> Prog (p2mr opening)
    , entryVectors = positive ++ negatives
    }]
 where
  split delimiter xs = case break (== delimiter) xs of
    (a, []) -> [a]
    (a, _:rest) -> a : split delimiter rest
