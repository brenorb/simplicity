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
  , runEntryIO
  , runVector
  , parallelIO
  , jetName
  , budgetMax
  , witnessBudgetModel
  ) where

import Control.Concurrent (forkIO, getNumCapabilities)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Concurrent.QSem (newQSem, waitQSem, signalQSem)
import Control.Exception (SomeException, bracket_, evaluate, throwIO, try)
import Control.Monad (forM)
import Data.List (sortBy, foldl')
import qualified Simplicity.Ty as Ty
import qualified Data.Map.Strict as Map
import Data.Ord (comparing, Down(..))
import Data.Word (Word64)

import Simplicity.Digest (Hash256)
import Simplicity.MerkleRoot (CommitmentRoot, commitmentRoot)
import Simplicity.Ty (SomeArrow(..))
import Simplicity.Weight (milliWeight)
import qualified Simplicity.Bitcoin.Dag as Dag
import qualified Simplicity.Bitcoin.Inference as Inference
import qualified Simplicity.Bitcoin.Serialization.BitString as Bits
import qualified Simplicity.Bitcoin.JetType as JT
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Jets (unwrap)

import JetDiscovery.Cost (TermWeight, milliWeigh)
import JetDiscovery.JetSets (PrimOnly(..), Ablate, NoSecpCurve, NoSecp, NoSha256, secpCurveJet, secpJet, sha256Jet)
import JetDiscovery.Profile (NodeInfo(..), profile)
import JetDiscovery.Types
import JetDiscovery.Tx (hashToInteger)
import JetDiscovery.WhatIf (WhatIf(..))
import JetDiscovery.JetSets (Candidate(..))
import JetDiscovery.Candidates.Impact (isolatedCosts)
import JetDiscovery.Reprice (primitiveCost,restrictedCost)

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
  , mCandidateCosts :: [(String,(Integer,Integer))] -- ^ candidate -> (isolated ESTIMATE milliWU, static multiplicity)
  , mProfileTotal :: Integer  -- ^ consistency check: must equal 'mCost'
  , mAblations :: [(String, Integer)]  -- ^ milliWU with a jet family removed (only when the program uses that family)
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
  { mCmr = commitmentRoot (unwrap jetted :: CommitmentRoot () ())
  , mCost = nativeCost
  , mCostBase = primitiveCost dag
  , mCostWhatIf = milliWeigh checkedWhatIf
  , mProgBits = length progBits
  , mWitBits = length witBits
  , mNodes = length prof
  , mProfile = prof
  , mWhatIfJets = Map.toList $ Map.fromListWith (+)
      [ (niKind ni, niMult ni) | ni <- whatIfProf, take 9 (niKind ni) == "jet:cand:" ]
  , mCandidateCosts = isolatedCosts nativeCost [drop 9 (niKind n)|n<-whatIfProf,take 9 (niKind n)=="jet:cand:"] whatIfDag
  , mProfileTotal = sum [ niMult ni * niSelf ni | ni <- prof ]
  , mAblations = [ (n, c) | (n, used, c) <- ablations, used ]
  }
 where
  -- Reuse the exact in-tree DAG and serializers. The public putTerm helper
  -- calls jetDag itself; calling it separately would repeat a large build.
  jetted = Jets.jetSubst (t :: Dag.JetDag Jets.JetType () ())
  nativeCost = milliWeigh (unwrap jetted :: TermWeight () ())
  progBits = Bits.putDagNoWitnessLengthCode dag
  witBits = maybe (error "invalid corpus witness encoding") id (Bits.putWitnessData dag)
  dag = Dag.jetDag (t :: Dag.JetDag Jets.JetType () ())
  prof = profile jetName (\j -> milliWeight (JT.jetCost j)) constValue dag
  constValue :: Jets.JetType a b -> Maybe Word64
  constValue j@(Jets.ConstWordJet _) = Just (fromIntegral (length (show j)) * 1000003 + fromIntegral (sum (map fromEnum (show j))))
  constValue _ = Nothing
  usesFamily f = any (\ni -> take 4 (niKind ni) == "jet:" && f (drop 4 (niKind ni))) prof
  ablations =
    [(name,usesFamily family,restrictedCost name dag)| (name,family)<-
      [("no-secp-curve",secpCurveJet),("no-secp",secpJet),("no-sha256",sha256Jet)]]
  -- Both consumers use the same fully inferred overlay DAG, avoiding a
  -- retained unjetted overlay while a second interpretation is constructed.
  whatIfDag = Dag.jetDag (t :: Dag.JetDag WhatIf () ())
  checkedWhatIf :: TermWeight () ()
  checkedWhatIf = either (error . ("overlay type check: " ++)) id (Inference.typeCheck whatIfDag)
  whatIfProf = profile whatIfName (\j -> milliWeight (JT.jetCost j)) (const Nothing) whatIfDag
  whatIfName :: WhatIf a b -> String
  whatIfName (Known j) = jetName j
  whatIfName (Cand c) = "cand:" ++ candName c

data VectorResult = VectorResult
  { vrName :: String
  , vrExpect :: Expect
  , vrOk :: Bool       -- ^ the program's outcome matches 'vrExpect'
  , vrNote :: String
  }

-- | Run one test vector with 'Jets.fastEval'.  Also checks that the CMR does not depend on the witness.
runVector :: (w -> Prog) -> Hash256 -> Vector w -> VectorResult
runVector prog cmr0 (Vector nm env w ex) =
  case env cmr of
    Nothing -> VectorResult nm ex False "environment construction failed"
    Just e ->
      -- Execute the jet-substituted program: that is the program a spender would publish,
      -- and jet substitution changes the CMRs that 'disconnect' commits to.
      let accepted = Jets.fastEval (unwrap wrapped) e () == Just ()
          ok = (ex == Accept) == accepted && cmr == cmr0
          note | cmr /= cmr0 = "CMR depends on witness"
               | otherwise = if accepted then "accepted" else "rejected"
      in VectorResult nm ex ok note
 where
  -- One traversal of the full (unjetted) term per vector, shared by the CMR check and execution.
  wrapped = Jets.jetSubst (unProg (prog w))
  cmr = commitmentRoot (unwrap wrapped :: CommitmentRoot () ())

runVectors :: (w -> Prog) -> Hash256 -> [Vector w] -> [VectorResult]
runVectors prog cmr0 = map (runVector prog cmr0)

data EntryResult = EntryResult
  { erEntry :: Entry
  , erMeasure :: Measurement
  , erVectors :: [VectorResult]
  }

-- | Measure an entry (using its first vector's witness) and run all its vectors, in parallel.
runEntryIO :: Entry -> IO EntryResult
runEntryIO e@(Entry _ _ _ _ _ _ prog vecs) = do
  let m = case vecs of
            (v:_) -> measure (prog (vecWitness v))
            [] -> error "runEntry: entry has no vectors"
      -- Finish both consumers of the candidate DAG together. Otherwise a
      -- completed cost can retain its large source DAG until candidate counts
      -- are requested after a second interpretation has already been built.
      forceWhatIf = mCostWhatIf m `seq` forcePairs (mWhatIfJets m) `seq`
        foldl' (\() (name,(cost,count))->forceText name `seq` cost `seq` count `seq` ()) () (mCandidateCosts m)
      forceProfile = mProfileTotal m `seq` foldl' (\() n -> forceNode n) () (mProfile m)
      forceM = [ () <$ evaluate (mCmr m), () <$ evaluate (mCost m), () <$ evaluate (mCostBase m)
               , evaluate forceWhatIf, () <$ evaluate (mProgBits m + mWitBits m)
               , evaluate forceProfile ]
               ++ [ () <$ evaluate c | (_, c) <- mAblations m ]
  _ <- parallelIO forceM
  vs <- parallelIO [ evaluate (forceVR (runVector prog (mCmr m) v)) | v <- vecs ]
  return (EntryResult e m vs)
 where
  forceVR r = vrOk r `seq` length (vrNote r) `seq` r
  forceText = foldl' (\() c -> fromEnum c `seq` ()) ()
  forcePairs = foldl' (\() (name,n) -> forceText name `seq` n `seq` ()) ()
  forceType = Ty.memoCataTy (\f -> case f of
    Ty.One -> (); Ty.Sum a b -> a `seq` b `seq` (); Ty.Prod a b -> a `seq` b `seq` ())
  forceNode n = niCmr n `seq` forceText (niKind n) `seq`
    forceType (niSrc n) `seq` forceType (niTgt n) `seq` ()

-- | Run actions concurrently (bounded by the number of capabilities) and collect results in order.
parallelIO :: [IO a] -> IO [a]
parallelIO acts = do
  n <- getNumCapabilities
  if n<=1 then sequence acts else do
    sem <- newQSem n
    vars <- forM acts $ \a -> do
      v <- newEmptyMVar
      _ <- forkIO $ bracket_ (waitQSem sem) (signalQSem sem) (try a >>= putMVar v)
      return v
    forM vars $ \v -> takeMVar v >>= either (\ex -> throwIO (ex :: SomeException)) return

-- | Measure an entry (using its first vector's witness) and run all its vectors.
runEntry :: Entry -> EntryResult
runEntry e@(Entry _ _ _ _ _ _ prog vecs) = EntryResult e m (runVectors prog (mCmr m) vecs)
 where
  m = case vecs of
        (v:_) -> measure (prog (vecWitness v))
        [] -> error "runEntry: entry has no vectors"
