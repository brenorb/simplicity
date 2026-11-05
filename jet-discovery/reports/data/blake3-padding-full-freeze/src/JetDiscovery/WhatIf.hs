{-# LANGUAGE GADTs, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
-- | The what-if jet set: every existing Bitcoin jet, plus the candidate jets
-- registered in "JetDiscovery.Candidates.Registry", priced at their ESTIMATE
-- costs.  The real jet tables and cost tables are never modified.
module JetDiscovery.WhatIf
  ( WhatIf(..)
  , whatIfMap
  ) where

import Control.Applicative ((<|>))
import Control.Arrow (runKleisli)
import Control.Monad.Trans.Reader (runReaderT)
import qualified Data.Map as Map
import Data.Type.Equality ((:~:)(Refl))

import Simplicity.Digest (Hash256)
import Simplicity.MerkleRoot (IdentityRoot, identityHash)
import Simplicity.Tensor (Product(..))
import Simplicity.Ty (TyC, someArrowMap, reifyArrow, equalTyReflect)
import qualified Simplicity.Bitcoin.JetType as JT
import qualified Simplicity.Bitcoin.Jets as Jets

import JetDiscovery.JetSets (Candidate(..), SomeCandidate(..), candidateRegistry)
import JetDiscovery.Candidates.Registry (candidates)

-- | Existing Bitcoin jets plus candidate jets.
data WhatIf a b = Known (Jets.JetType a b) | Cand (Candidate a b)

{-# NOINLINE whatIfMap #-}
-- | Registered candidates indexed by the identity Merkle root of their specification.
whatIfMap :: Map.Map Hash256 SomeCandidate
whatIfMap = candidateRegistry candidates

instance JT.JetType WhatIf where
  type MatcherInfo WhatIf = Product (JT.MatcherInfo Jets.JetType) IdentityRoot
  specification (Known j) = JT.specification j
  specification (Cand (Candidate _ _ spec)) = spec
  implementation (Known j) = JT.implementation j
  implementation (Cand (Candidate _ _ spec)) = flip $ runReaderT . runKleisli spec
  -- An existing jet always wins over a candidate with the same identity root.
  matcher (Product mk ir) = (Known <$> JT.matcher mk) <|> lookupCand
   where
    lookupCand = do
      SomeCandidate c <- Map.lookup (identityHash ir) whatIfMap
      let (ira, irb) = reifyArrow ir
          (ca, cb) = reifyArrow (specOf c)
      case (equalTyReflect ira ca, equalTyReflect irb cb) of
        (Just Refl, Just Refl) -> Just (Cand c)
        _ -> Nothing
  getJetBit abort next = someArrowMap Known <$> JT.getJetBit abort next
  putJetBit (Known j) = JT.putJetBit j
  putJetBit (Cand _) = error "WhatIf: candidate jets have no serialization"
  jetCost (Known j) = JT.jetCost j
  jetCost (Cand c) = candCost c

specOf :: (TyC a, TyC b) => Candidate a b -> IdentityRoot a b
specOf (Candidate _ _ spec) = spec
