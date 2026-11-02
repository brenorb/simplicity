-- | Plain-text reports (Markdown and TSV).  Every number comes from 'JetDiscovery.Run'.
module JetDiscovery.Report
  ( wu
  , pct
  , resultsMarkdown
  , resultsTsv
  , vectorsOk
  ) where

import Data.List (intercalate)
import Numeric (showFFloat)

import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx (hex, hashToBytes)

-- | Render milliWU as WU with three decimals.
wu :: Integer -> String
wu m = showFFloat (Just 3) (fromInteger m / 1000 :: Double) ""

pct :: Integer -> Integer -> String
pct a b | b == 0 = "-"
        | otherwise = showFFloat (Just 2) (100 * fromInteger a / fromInteger b :: Double) "%"

vectorsOk :: EntryResult -> Bool
vectorsOk = all vrOk . erVectors

-- | Estimated witness stack bytes for a script-path spend: program, witness,
-- CMR (32), control block (33 for a single leaf), plus 4 length prefix bytes.
witnessStackBytes :: Measurement -> Integer
witnessStackBytes m = bytes (mProgBits m) + bytes (mWitBits m) + 32 + 33 + 4
 where bytes b = (toInteger b + 7) `div` 8

resultsMarkdown :: [EntryResult] -> String
resultsMarkdown rs = unlines $
  [ "| id | category | vectors | cost (WU) | prims-only baseline (WU) | jet saving | what-if (WU) | % of BUDGET_MAX | program bytes | witness bytes | assumed budget (WU) | fits assumed budget |"
  , "| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |" ] ++
  map row rs
 where
  row r = let e = erEntry r; m = erMeasure r
              wsb = witnessStackBytes m
              budget = witnessBudgetModel wsb
              vs = erVectors r
          in "| `" ++ entryId e ++ "` | " ++ show (entryCategory e)
             ++ " | " ++ show (length (filter vrOk vs)) ++ "/" ++ show (length vs)
             ++ " | " ++ wu (mCost m) ++ " | " ++ wu (mCostBase m)
             ++ " | " ++ ratio (mCostBase m) (mCost m)
             ++ " | " ++ wu (mCostWhatIf m)
             ++ " | " ++ pct (mCost m) (budgetMax * 1000)
             ++ " | " ++ show ((mProgBits m + 7) `div` 8) ++ " | " ++ show ((mWitBits m + 7) `div` 8)
             ++ " | " ++ show budget
             ++ " | " ++ (if mCost m <= budget * 1000 then "yes" else "no (+" ++ wu (mCost m - budget * 1000) ++ " WU padding)")
             ++ " |"
  ratio a b | b == 0 = "-"
            | otherwise = showFFloat (Just 1) (fromInteger a / fromInteger b :: Double) "×"

resultsTsv :: [EntryResult] -> String
resultsTsv rs = unlines $
  intercalate "\t" ["id","category","vectors_ok","vectors_total","cost_mwu","baseline_mwu","whatif_mwu","program_bits","witness_bits","dag_nodes","cmr"] :
  [ intercalate "\t" [ entryId e, show (entryCategory e), show (length (filter vrOk vs)), show (length vs)
                     , show (mCost m), show (mCostBase m), show (mCostWhatIf m)
                     , show (mProgBits m), show (mWitBits m), show (mNodes m), hex (hashToBytes (mCmr m)) ]
  | r <- rs, let e = erEntry r; m = erMeasure r; vs = erVectors r ]
