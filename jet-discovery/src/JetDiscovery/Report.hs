-- | Plain-text reports (Markdown and TSV).  Every number comes from 'JetDiscovery.Run'.
module JetDiscovery.Report
  ( wu
  , pct
  , resultsMarkdown
  , resultsTsv
  , vectorsOk
  , whatIfMarkdown
  , ablationMarkdown
  , witnessStackBytes
  , assumedWitnessStackBytes
  , candidateImpactMarkdown
  , candidateImpactTsv
  ) where

import Data.List (intercalate)
import Numeric (showFFloat, showEFloat)

import JetDiscovery.Profile (niCmr)
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
vectorsOk r = all vrOk (erVectors r) && mProfileTotal m == mCost m &&
  not (null (mProfile m)) && niCmr (last (mProfile m)) == mCmr m
 where m = erMeasure r

-- | Hypothetical four-element script-path stack: program, witness, CMR (32),
-- control block (33 for a single leaf). Includes CompactSize count/lengths.
-- This is an explicit budget scenario, not a Bitcoin integration rule.
witnessStackBytes :: Measurement -> Integer
witnessStackBytes m = assumedWitnessStackBytes [bytes (mProgBits m),bytes (mWitBits m),32,33]
 where bytes b = (toInteger b + 7) `div` 8

assumedWitnessStackBytes :: [Integer] -> Integer
assumedWitnessStackBytes sizes = compactSize (toInteger (length sizes)) + sum [compactSize n+n | n<-sizes]
 where
  compactSize n | n<0=error "negative witness element length"
                | n<253=1
                | n<=65535=3
                | n<=4294967295=5
                | n<=18446744073709551615=9
                | otherwise=error "witness element exceeds CompactSize"

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
             ++ " | " ++ wu (mCost m) ++ " | " ++ sciWu (mCostBase m)
             ++ " | " ++ ratio (mCostBase m) (mCost m)
             ++ " | " ++ wu (mCostWhatIf m)
             ++ " | " ++ pct (mCost m) (budgetMax * 1000)
             ++ " | " ++ show ((mProgBits m + 7) `div` 8) ++ " | " ++ show ((mWitBits m + 7) `div` 8)
             ++ " | " ++ show budget
             ++ " | " ++ (if mCost m <= budget * 1000 then "yes" else "no (" ++ wu (mCost m - budget * 1000) ++ " WU deficit)")
             ++ " |"
  ratio a b | b == 0 = "-"
            | otherwise = let x = fromInteger a / fromInteger b :: Double in if x < 1e6 then showFFloat (Just 1) x "×" else showEFloat (Just 1) x "×"
  sciWu x | x < 10 ^ (12 :: Int) = wu x
          | otherwise = showEFloat (Just 2) (fromInteger x / 1000 :: Double) ""

resultsTsv :: [EntryResult] -> String
resultsTsv rs = unlines $
  intercalate "\t" ["id","category","vectors_ok","vectors_total","cost_mwu","baseline_mwu","whatif_mwu","program_bits","witness_bits","dag_nodes","cmr"] :
  [ intercalate "\t" [ entryId e, show (entryCategory e), show (length (filter vrOk vs)), show (length vs)
                     , show (mCost m), show (mCostBase m), show (mCostWhatIf m)
                     , show (mProgBits m), show (mWitBits m), show (mNodes m), hex (hashToBytes (mCmr m)) ]
  | r <- rs, let e = erEntry r; m = erMeasure r; vs = erVectors r ]

-- | One-candidate-at-a-time counterfactuals, including nested matches and
-- worst-branch changes. Different rows are alternatives and are not additive.
candidateImpactMarkdown :: [EntryResult] -> String
candidateImpactMarkdown rs=unlines $
  ["| program | candidate | isolated occurrences | current WU | isolated WU (ESTIMATE) | WU saved | fits fixed hypothetical budget, before / after |",
   "| --- | --- | ---: | ---: | ---: | ---: | --- |"]++
  ["| `"++entryId (erEntry r)++"` | ["++name++"](../candidates/"++name++"/README.md) | "++show count++" | "++wu (mCost m)++" | "++wu after++" | "++wu (mCost m-after)++" | "++fits (mCost m)++" / "++fits after++" |"
  |r<-rs,let m=erMeasure r,(name,(after,count))<-mCandidateCosts m,count>0,
   let fits cost=if cost<=1000*witnessBudgetModel (witnessStackBytes m) then "yes" else "no"]

candidateImpactTsv :: [EntryResult] -> String
candidateImpactTsv rs=unlines $ intercalate "\t" ["program","candidate","occurrences","current_mwu","isolated_mwu_estimate","saving_mwu","assumed_budget_wu"]:
  [intercalate "\t" [entryId (erEntry r),name,show count,show (mCost m),show after,show (mCost m-after),show (witnessBudgetModel (witnessStackBytes m))]
  |r<-rs,let m=erMeasure r,(name,(after,count))<-mCandidateCosts m]

-- | Per-program what-if: which candidates matched (with multiplicity) and the new bound.
whatIfMarkdown :: [EntryResult] -> String
whatIfMarkdown rs = unlines $
  [ "| id | cost (WU) | what-if cost (WU, ESTIMATE) | saving | candidates matched (multiplicity in the static bound) |"
  , "| --- | ---: | ---: | ---: | --- |" ] ++
  [ "| `" ++ entryId (erEntry r) ++ "` | " ++ wu (mCost m) ++ " | " ++ wu (mCostWhatIf m) ++ " | " ++ saving
    ++ " | " ++ intercalate ", " [ drop 9 k ++ " ×" ++ show n | (k, n) <- mWhatIfJets m ] ++ " |"
  | r <- rs, let m = erMeasure r, not (null (mWhatIfJets m))
  , let saving = showFFloat (Just 1) (fromInteger (mCost m) / fromInteger (max 1 (mCostWhatIf m)) :: Double) "×" ]

-- | Per-program cost with jet families removed.
ablationMarkdown :: [EntryResult] -> String
ablationMarkdown rs = unlines $
  [ "| id | cost (WU) | no secp256k1 curve/signature jets (WU) | no secp256k1 jets at all (WU) | no SHA-256 jets (WU) |"
  , "| --- | ---: | ---: | ---: | ---: |" ] ++
  [ "| `" ++ entryId (erEntry r) ++ "` | " ++ wu (mCost m) ++ " | " ++ col "no-secp-curve" ++ " | " ++ col "no-secp" ++ " | " ++ col "no-sha256" ++ " |"
  | r <- rs, let m = erMeasure r, not (null (mAblations m))
  , let col n = maybe "-" sci (lookup n (mAblations m)) ]
 where
  sci x | x < 10 ^ (12 :: Int) = wu x
        | otherwise = let d = fromInteger x / 1000 :: Double in showEFloat (Just 2) d ""
