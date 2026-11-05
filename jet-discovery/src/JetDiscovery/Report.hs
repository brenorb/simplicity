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
  , budgetHotspotsMarkdown
  , budgetHotspotsTsv
  ) where

import Data.List (intercalate, isPrefixOf, maximumBy, sortOn)
import qualified Data.Map.Strict as Map
import Data.Ord (Down(..), comparing)
import Numeric (showFFloat, showEFloat)

import JetDiscovery.Profile (NodeInfo(..))
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx (hex, hashToBytes)

-- This explicit annotation is part of a client's declared interface. A
-- deliberately invalid virtual proof transaction cannot establish deployment
-- feasibility, even though its statement has a measurable interpreter cost.
clientMode :: Entry -> Bool
clientMode = any (isPrefixOf "CLIENT MODE:") . entryAssumptions

executionContext :: Entry -> String
executionContext e = if clientMode e then "client-verifier" else "transaction-expression"

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
  [ "| id | category | execution context | vectors | cost (WU) | prims-only baseline (WU) | jet saving | what-if (WU) | % of BUDGET_MAX | program bytes | witness bytes | raw hypothetical budget (WU) | fits capped hypothetical budget |"
  , "| --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |" ] ++
  map row rs
 where
  row r = let e = erEntry r; m = erMeasure r
              wsb = witnessStackBytes m
              rawBudget = witnessBudgetModel wsb
              budget = min budgetMax rawBudget
              vs = erVectors r
          in "| `" ++ entryId e ++ "` | " ++ show (entryCategory e)
             ++ " | " ++ executionContext e
             ++ " | " ++ show (length (filter vrOk vs)) ++ "/" ++ show (length vs)
             ++ " | " ++ wu (mCost m) ++ " | " ++ sciWu (mCostBase m)
             ++ " | " ++ ratio (mCostBase m) (mCost m)
             ++ " | " ++ wu (mCostWhatIf m)
             ++ " | " ++ pct (mCost m) (budgetMax * 1000)
             ++ " | " ++ show ((mProgBits m + 7) `div` 8) ++ " | " ++ show ((mWitBits m + 7) `div` 8)
             ++ " | " ++ show rawBudget
             ++ " | " ++ (if clientMode e then "n/a (client verifier)" else if mCost m <= budget * 1000 then "yes" else "no (" ++ wu (mCost m - budget * 1000) ++ " WU deficit)")
             ++ " |"
  ratio a b | b == 0 = "-"
            | otherwise = let x = fromInteger a / fromInteger b :: Double in if x < 1e6 then showFFloat (Just 1) x "×" else showEFloat (Just 1) x "×"
  sciWu x | x < 10 ^ (12 :: Int) = wu x
          | otherwise = showEFloat (Just 2) (fromInteger x / 1000 :: Double) ""

resultsTsv :: [EntryResult] -> String
resultsTsv rs = unlines $
  intercalate "\t" ["id","category","vectors_ok","vectors_total","cost_mwu","baseline_mwu","whatif_mwu","program_bits","witness_bits","dag_nodes","cmr","execution_context"] :
  [ intercalate "\t" [ entryId e, show (entryCategory e), show (length (filter vrOk vs)), show (length vs)
                     , show (mCost m), show (mCostBase m), show (mCostWhatIf m)
                     , show (mProgBits m), show (mWitBits m), show (mNodes m), hex (hashToBytes (mCmr m)), executionContext e ]
  | r <- rs, let e = erEntry r; m = erMeasure r; vs = erVectors r ]

-- | One-candidate-at-a-time counterfactuals, including nested matches and
-- worst-branch changes. Different rows are alternatives and are not additive.
candidateImpactMarkdown :: [EntryResult] -> String
candidateImpactMarkdown rs=unlines $
  ["| program | candidate | selected-path occurrences | matched DAG nodes | current WU | isolated WU (ESTIMATE) | WU saved | fits fixed hypothetical budget, before / after |",
   "| --- | --- | ---: | ---: | ---: | ---: | ---: | --- |"]++
  ["| `"++entryId (erEntry r)++"` | ["++name++"](../candidates/"++name++"/README.md) | "++show count++" | "++show sites++" | "++wu (mCost m)++" | "++wu after++" | "++wu (mCost m-after)++" | "++fits (mCost m)++" / "++fits after++" |"
  |r<-rs,let m=erMeasure r,(name,(after,count,sites))<-mCandidateCosts m,sites>0 || mCost m/=after,
   let fits cost=if clientMode (erEntry r) then "n/a (client verifier)" else if cost<=1000*min budgetMax (witnessBudgetModel (witnessStackBytes m)) then "yes" else "no"]

candidateImpactTsv :: [EntryResult] -> String
candidateImpactTsv rs=unlines $ intercalate "\t" ["program","candidate","occurrences","matched_dag_nodes","current_mwu","isolated_mwu_estimate","saving_mwu","assumed_budget_wu","maximum_budget_wu","effective_budget_wu","execution_context","feasibility_applicable"]:
  [intercalate "\t" [entryId (erEntry r),name,show count,show sites,show (mCost m),show after,show (mCost m-after),show budget,show budgetMax,show (min budget budgetMax),executionContext (erEntry r),if clientMode (erEntry r) then "false" else "true"]
  |r<-rs,let m=erMeasure r,(name,(after,count,sites))<-mCandidateCosts m,let budget=witnessBudgetModel (witnessStackBytes m)]

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

-- | Separate unique and shared node contributions even when the global mining
-- table omits them. Group exclusive weight by exact jet/combinator kind. The
-- group totals partition the bound; nested inclusive costs would overlap.
budgetHotspots :: [EntryResult] -> [(EntryResult,Integer,[(String,Integer)],NodeInfo)]
budgetHotspots rs =
  [ (r,budget,byKind,heaviest)
  | r <- rs, let e=erEntry r; m=erMeasure r
  , not (clientMode e)
  , let budget=witnessBudgetModel (witnessStackBytes m)
  , mCost m > 1000*min budget budgetMax
  , let nodes=mProfile m
        self n=niMult n*niSelf n
        byKind=sortOn (\(kind,c)->(Down c,kind)) . Map.toList $
          Map.fromListWith (+) [(niKind n,self n) | n<-nodes, self n>0]
        heaviest=maximumBy (comparing (\n->(self n,Down (niIndex n)))) nodes
  ]

budgetHotspotsMarkdown :: [EntryResult] -> String
budgetHotspotsMarkdown rs = unlines $
  [ "# What dominates over-budget programs"
  , ""
  , "Every non-client program above its first-vector witness-stack-bytes + 50 WU scenario or the in-tree maximum caller budget appears below. The first comparison is hypothetical. The per-kind values sum exclusive node weight times selected-path multiplicity; they partition the bound, including unique nodes. The separate largest node uses its own exclusive contribution. Ablations reprice the original expression with the named jet family removed."
  , ""
  , "| program | native WU | raw hypothetical budget WU | capped deficit WU | above maximum caller budget | largest exclusive contributors (WU, share) | largest exact node (CMR and exclusive WU) | largest ablation increase WU |"
  , "| --- | ---: | ---: | ---: | --- | --- | --- | ---: |"
  ] ++ map row (budgetHotspots rs)
 where
  row (r,budget,byKind,node) = intercalate " | "
    ["| `"++entryId (erEntry r)++"`",wu (mCost m),show budget,wu (max 0 (mCost m-1000*min budget budgetMax)),
     if mCost m>1000*budgetMax then "yes" else "no",
     intercalate "; " [kind++" "++wu c++" ("++pct c (mCost m)++")" | (kind,c)<-take 5 byKind],
     niKind node++" `"++hex (hashToBytes (niCmr node))++"` "++wu (niSelf node*niMult node),
     ablation m++" |"]
   where m=erMeasure r
  ablation m = case sortOn (Down . snd) [(n,c-mCost m) | (n,c)<-mAblations m,c>mCost m] of
    (name,increase):_ -> name++" "++wu increase
    [] -> "—"

budgetHotspotsTsv :: [EntryResult] -> String
budgetHotspotsTsv rs = unlines $
  "program\tnative_mwu\tassumed_budget_wu\tmaximum_budget_wu\tkind\texclusive_mwu" :
  [intercalate "\t" [entryId (erEntry r),show (mCost (erMeasure r)),show budget,show budgetMax,kind,show c]
  | (r,budget,byKind,_)<-budgetHotspots rs,(kind,c)<-byKind]
