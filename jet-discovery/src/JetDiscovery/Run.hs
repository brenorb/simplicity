{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}
-- | Measuring and testing corpus programs.
module JetDiscovery.Run
  ( Measurement(..)
  , measure
  , progCmr
  , VectorResult(..)
  , runVectors
  , EntryResult(..)
  , runEntry
  , jetName
  , budgetMax
  , witnessBudgetModel
  ) where

import Data.List (sortBy)
import qualified Data.Map.Strict as Map
import Data.Ord (comparing, Down(..))
import Data.Word (Word64)

import Simplicity.Digest (Hash256)
import Simplicity.MerkleRoot (CommitmentRoot, commitmentRoot)
import Simplicity.Ty (SomeArrow(..))
import Simplicity.Weight (milliWeight)
import qualified Simplicity.Bitcoin.Dag as Dag
import qualified Simplicity.Bitcoin.JetType as JT
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Jets (unwrap)

import JetDiscovery.Cost (TermWeight, milliWeigh)
import JetDiscovery.JetSets (PrimOnly(..))
import JetDiscovery.Profile (NodeInfo(..), profile)
import JetDiscovery.Types
import JetDiscovery.Tx (hashToInteger)
import JetDiscovery.WhatIf (WhatIf(..))
import JetDiscovery.JetSets (Candidate(..))

-- | BUDGET_MAX from C/limitations.h, in WU.
budgetMax :: Integer
budgetMax = 4000050

-- | ASSUMPTION (not defined in this repository): a BIP 342 style budget equal
-- to the serialized witness size plus 50 WU.  C/bitcoin/exec.c takes the budget
-- as a caller-supplied parameter, so the Bitcoin rule is still open.
-- Returns the budget in WU for a witness stack of the given number of bytes.
witnessBudgetModel :: Integer -> Integer
witnessBudgetModel witnessBytes = witnessBytes + 50

data Measurement = Measurement
  { mCmr        :: Hash256
  , mCost       :: Integer   -- ^ milliWU, existing Bitcoin jets
  , mCostBase   :: Integer   -- ^ milliWU, primitive jets only
  , mCostWhatIf :: Integer   -- ^ milliWU, existing jets + candidates (ESTIMATE)
  , mProgBits   :: Int
  , mWitBits    :: Int
  , mNodes      :: Int
  , mProfile    :: [NodeInfo]  -- ^ profile of the jetted DAG
  , mWhatIfJets :: [(String, Integer)]  -- ^ candidates matched, with multiplicity
  , mProfileTotal :: Integer  -- ^ consistency check: must equal 'mCost'
  }

-- | Display name of a jet, e.g. @Sha256Block@.
jetName :: Jets.JetType a b -> String
jetName (Jets.ConstWordJet _) = "ConstWord"
jetName j = last (words (filter (`notElem` "()") (show j)))

-- | CMR of the jet-substituted program (the CMR committed to in the taproot leaf).
progCmr :: Prog -> Hash256
progCmr (Prog t) = commitmentRoot (unwrap (Jets.jetSubst t) :: CommitmentRoot () ())

measure :: Prog -> Measurement
measure (Prog t) = Measurement
  { mCmr = commitmentRoot (unwrap (Jets.jetSubst t) :: CommitmentRoot () ())
  , mCost = milliWeigh (unwrap (Jets.jetSubst t) :: TermWeight () ())
  , mCostBase = milliWeigh (unwrap (Dag.jetSubst (t :: Dag.JetDag PrimOnly () ())) :: TermWeight () ())
  , mCostWhatIf = milliWeigh (unwrap (Dag.jetSubst whatIfDag) :: TermWeight () ())
  , mProgBits = length progBits
  , mWitBits = length witBits
  , mNodes = length prof
  , mProfile = prof
  , mWhatIfJets = Map.toList $ Map.fromListWith (+)
      [ (niKind ni, niMult ni) | ni <- whatIfProf, take 9 (niKind ni) == "jet:cand:" ]
  , mProfileTotal = sum [ niMult ni * niSelf ni | ni <- prof ]
  }
 where
  (progBits, witBits) = Jets.putTermLengthCode t
  dag = Dag.jetDag (t :: Dag.JetDag Jets.JetType () ())
  prof = profile jetName (\j -> milliWeight (JT.jetCost j)) constValue dag
  constValue :: Jets.JetType a b -> Maybe Word64
  constValue j@(Jets.ConstWordJet _) = Just (fromIntegral (length (show j)) * 1000003 + fromIntegral (sum (map fromEnum (show j))))
  constValue _ = Nothing
  whatIfDag = t :: Dag.JetDag WhatIf () ()
  whatIfProf = profile whatIfName (\j -> milliWeight (JT.jetCost j)) (const Nothing) (Dag.jetDag whatIfDag)
  whatIfName :: WhatIf a b -> String
  whatIfName (Known j) = jetName j
  whatIfName (Cand c) = "cand:" ++ candName c

data VectorResult = VectorResult
  { vrName :: String
  , vrExpect :: Expect
  , vrOk :: Bool       -- ^ the program's outcome matches 'vrExpect'
  , vrNote :: String
  }

-- | Run every test vector with 'Jets.fastEval'.  Also checks that the CMR does not depend on the witness.
runVectors :: (w -> Prog) -> Hash256 -> [Vector w] -> [VectorResult]
runVectors prog cmr0 = map run1
 where
  run1 (Vector nm env w ex) =
    case env cmr of
      Nothing -> VectorResult nm ex False "environment construction failed"
      Just e ->
        -- Execute the jet-substituted program: that is the program a spender would publish,
        -- and jet substitution changes the CMRs that 'disconnect' commits to.
        let accepted = Jets.fastEval (unwrap (Jets.jetSubst (unProg (prog w)))) e () == Just ()
            ok = (ex == Accept) == accepted && cmr == cmr0
            note | cmr /= cmr0 = "CMR depends on witness"
                 | otherwise = if accepted then "accepted" else "rejected"
        in VectorResult nm ex ok note
   where
    cmr = commitmentRoot (unwrap (Jets.jetSubst (unProg (prog w))) :: CommitmentRoot () ())

data EntryResult = EntryResult
  { erEntry :: Entry
  , erMeasure :: Measurement
  , erVectors :: [VectorResult]
  }

-- | Measure an entry (using its first vector's witness) and run all its vectors.
runEntry :: Entry -> EntryResult
runEntry e@(Entry _ _ _ _ _ _ prog vecs) = EntryResult e m (runVectors prog (mCmr m) vecs)
 where
  m = case vecs of
        (v:_) -> measure (prog (vecWitness v))
        [] -> error "runEntry: entry has no vectors"
