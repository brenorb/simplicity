{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-full-laziness -fno-cse #-}
-- | Allocate a coarse existing-jet representation with the calling program's
-- lifetime. The expression stays a runtime argument of this opaque factory,
-- so a closed large transform is not floated into a permanent global CAF.
-- Keep the allocation flags confined to this tiny module: large recursive TyC
-- dictionaries in callers still need GHC's ordinary sharing optimizations.
module JetDiscovery.Lib.LocalTerm(localJetSubst)where
import Simplicity.Ty(TyC)
import Simplicity.Bitcoin.Term(Simplicity)
import qualified Simplicity.Bitcoin.Jets as J
{-# NOINLINE localJetSubst #-}
localJetSubst :: forall marker a b. (TyC a,TyC b)
 => marker -> (forall t. Simplicity t => t a b) -> J.WrappedSimplicity a b
localJetSubst marker expression=marker`seq`J.jetSubst expression
