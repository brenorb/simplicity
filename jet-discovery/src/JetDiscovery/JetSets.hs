{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances, KindSignatures #-}
-- | Alternative jet sets used for measurement.
--
-- * 'PrimOnly': only the jets that wrap transaction primitives (plus constant
--   words).  Bitcoin Simplicity exposes primitives only through jets, so this is
--   the cheapest set in which every corpus program is still expressible.  It is
--   the "unjetted" baseline.
--
-- * 'Candidate': a hypothetical jet (see "JetDiscovery.WhatIf").
module JetDiscovery.JetSets
  ( PrimOnly(..)
  , isPrimitiveJet
  , Candidate(..)
  , SomeCandidate(..)
  , candidateRegistry
  , Ablate(..), AblationPolicy(..), NoSecpCurve, NoSecp, NoSha256
  , secpCurveJet, secpJet, sha256Jet
  ) where

import Data.List (isPrefixOf)
import Data.Proxy (Proxy(..))

import qualified Data.Map as Map

import Simplicity.Digest (Hash256)
import Simplicity.MerkleRoot (IdentityRoot, identityHash)
import Simplicity.Ty (TyC, someArrowMap)
import Simplicity.Bitcoin.Term (Assert, Primitive)
import qualified Simplicity.Bitcoin.JetType as JT
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Weight (Weight)

-- | Existing Bitcoin jets restricted to primitive wrappers and constant words.
newtype PrimOnly a b = PrimOnly (Jets.JetType a b)

-- | True for jets whose specification is a single transaction primitive, and for constant words.
isPrimitiveJet :: Jets.JetType a b -> Bool
isPrimitiveJet (Jets.ConstWordJet _) = True
isPrimitiveJet (Jets.BitcoinJet (Jets.TransactionJet t)) = case t of
  Jets.ScriptCMR -> True
  Jets.InternalKey -> True
  Jets.CurrentIndex -> True
  Jets.LockTime -> True
  Jets.OutputValue -> True
  Jets.OutputScriptHash -> True
  Jets.InputPrevOutpoint -> True
  Jets.InputValue -> True
  Jets.InputScriptHash -> True
  Jets.InputSequence -> True
  Jets.InputAnnexHash -> True
  Jets.InputScriptSigHash -> True
  Jets.TapleafVersion -> True
  Jets.Tappath -> True
  Jets.Version -> True
  Jets.TransactionId -> True
  _ -> False
isPrimitiveJet _ = False

instance JT.JetType PrimOnly where
  type MatcherInfo PrimOnly = JT.MatcherInfo Jets.JetType
  specification (PrimOnly j) = JT.specification j
  implementation (PrimOnly j) = JT.implementation j
  matcher m = do
    j <- JT.matcher m
    if isPrimitiveJet j then Just (PrimOnly j) else Nothing
  getJetBit abort next = someArrowMap PrimOnly <$> JT.getJetBit abort next
  putJetBit (PrimOnly j) = JT.putJetBit j
  jetCost (PrimOnly j) = JT.jetCost j

-- | A hypothetical jet: a name, a Simplicity specification and an ESTIMATE cost.
data Candidate a b where
  Candidate :: (TyC a, TyC b)
            => { candName :: String
               , candCost :: Weight   -- ^ ESTIMATE; see candidates/<name>/README.md for the method
               , candSpec :: forall term. (Assert term, Primitive term) => term a b
               }
            -> Candidate a b

-- | A candidate with its types hidden.
data SomeCandidate where
  SomeCandidate :: (TyC a, TyC b) => Candidate a b -> SomeCandidate

-- | Index candidates by the identity Merkle root of their specification.
candidateRegistry :: [SomeCandidate] -> Map.Map Hash256 SomeCandidate
candidateRegistry cs = Map.fromList [ (identityHash (imr c), sc) | sc@(SomeCandidate c) <- cs ]
 where
  imr :: (TyC a, TyC b) => Candidate a b -> IdentityRoot a b
  imr (Candidate _ _ spec) = spec

-- Ablations ---------------------------------------------------------------------

-- | Jet families, by display name.
secpCurveJet, secpJet, sha256Jet :: String -> Bool
secpCurveJet n = any (`isPrefixOf` n)
  [ "Gej", "Ge", "Generate", "Scale", "LinearCombination", "LinearVerify", "PointVerify", "Decompress"
  , "Swu", "HashToCurve", "Bip0340", "CheckSig", "BuildTaptweak" ]
secpJet n = secpCurveJet n || "Fe" `isPrefixOf` n || "Scalar" `isPrefixOf` n
sha256Jet n = "Sha256" `isPrefixOf` n

-- | Policies naming the jets an ablated set drops.
class AblationPolicy p where
  policyName :: Proxy p -> String
  drops :: Proxy p -> String -> Bool

data NoSecpCurve
data NoSecp
data NoSha256
instance AblationPolicy NoSecpCurve where { policyName _ = "no-secp-curve"; drops _ = secpCurveJet }
instance AblationPolicy NoSecp where { policyName _ = "no-secp"; drops _ = secpJet }
instance AblationPolicy NoSha256 where { policyName _ = "no-sha256"; drops _ = sha256Jet }

-- | All existing Bitcoin jets except those the policy drops.
newtype Ablate p a b = Ablate (Jets.JetType a b)

ablateName :: Jets.JetType a b -> String
ablateName (Jets.ConstWordJet _) = "ConstWord"
ablateName j = last (words (filter (`notElem` "()") (show j)))

instance AblationPolicy p => JT.JetType (Ablate p) where
  type MatcherInfo (Ablate p) = JT.MatcherInfo Jets.JetType
  specification (Ablate j) = JT.specification j
  implementation (Ablate j) = JT.implementation j
  matcher m = do
    j <- JT.matcher m
    if drops (Proxy :: Proxy p) (ablateName j) then Nothing else Just (Ablate j)
  getJetBit abort next = someArrowMap Ablate <$> JT.getJetBit abort next
  putJetBit (Ablate j) = JT.putJetBit j
  jetCost (Ablate j) = JT.jetCost j
