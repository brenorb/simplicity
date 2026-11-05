{-# LANGUAGE ScopedTypeVariables #-}
-- | Reuse the existing-jet DAG as the source of restricted-set analyses.
-- Expand specifications and rerun full program type inference. Simply adding
-- fixed per-jet reference costs would miss type erasure outside removed jets
-- (for example an ignored half-word beside a projection).
module JetDiscovery.Reprice (primitiveCost,restrictedCost) where
import Data.Proxy (Proxy(..))
import Data.Sequence (Seq)
import Simplicity.Ty (Ty,UntypedValue,SomeArrow)
import qualified Simplicity.Bitcoin.Inference as I
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Dag as D
import JetDiscovery.Cost (TermWeight,milliWeigh)
import JetDiscovery.JetSets

type KnownDag=I.SimplicityDag Seq Ty (SomeArrow J.JetType) UntypedValue
primitiveCost :: KnownDag -> Integer
primitiveCost dag=milliWeigh (J.unwrap (D.jetSubst rebuilt) :: TermWeight () ())
 where
  rebuilt=either (error.("baseline reconstruction: "++)) id (I.typeCheck dag) :: D.JetDag PrimOnly () ()

restricted :: forall p. AblationPolicy p => Proxy p -> KnownDag -> Integer
restricted _ dag=milliWeigh (J.unwrap (D.jetSubst rebuilt) :: TermWeight () ())
 where
  rebuilt=either (error.("ablation reconstruction: "++)) id (I.typeCheck dag) :: D.JetDag (Ablate p) () ()
restrictedCost :: String -> KnownDag -> Integer
restrictedCost name=case name of
 "no-secp-curve"->restricted (Proxy :: Proxy NoSecpCurve)
 "no-secp"->restricted (Proxy :: Proxy NoSecp)
 "no-sha256"->restricted (Proxy :: Proxy NoSha256)
 _->error ("unknown ablation: "++name)
