{-# LANGUAGE ExistentialQuantification, RankNTypes, ScopedTypeVariables #-}
-- | Corpus entry types.
--
-- A corpus program is a Bitcoin Simplicity program of type @term () ()@ that
-- is parameterised by its witness data.  The witness only changes the
-- 'witness' nodes of the program, never its commitment Merkle root (CMR) or
-- its static cost.
module JetDiscovery.Types
  ( Prog(Prog, unProg)
  , boundProgram, BoundView(..), boundView
  , BoundKernel, boundTerm, boundFingerprint, boundEligible
  , Expect(..)
  , Vector(..)
  , Category(..)
  , Entry(..)
  , VectorSource(..)
  ) where

import Prelude hiding (drop, take, fail)
import Simplicity.Digest (Hash256, integerHash256)
import Simplicity.MerkleRoot (AnnotatedRoot, annotatedRoot)
import Simplicity.Bitcoin.Primitive (PrimEnv)
import Simplicity.Bitcoin.Term

-- | A complete Bitcoin Simplicity program, polymorphic in its interpretation.
data Prog
  = Prog { unProg :: forall term. (Simplicity term, Primitive term) => term () () }
  | forall a. TyC a => BoundProg
      { unProg :: forall term. (Simplicity term, Primitive term) => term () ()
      , boundInput :: a
      , boundKernel :: BoundKernel a
      }

-- | A shared, witness-free kernel. Its annotated root commits to types,
-- constants, primitive identities and hidden assertion roots. It deliberately
-- holds no compiled DAG: the runner releases that graph after one vector batch.
data BoundKernel a = BoundKernel
  { boundTerm :: forall term. (Simplicity term, Primitive term) => term a ()
  , boundFingerprint :: Hash256
  , boundEligible :: Bool
  }

data BoundView = forall a. TyC a => BoundView (BoundKernel a) a

boundView :: Prog -> Maybe BoundView
boundView (BoundProg _ value kernel) = Just (BoundView kernel value)
boundView _ = Nothing

-- | Partially apply this to a kernel outside the per-vector encoder. The
-- canonical program is exactly one witness followed by that kernel; cost and
-- serialization still consume this complete expression through 'unProg'.
-- Internal witnesses or delegation conservatively disable prepared execution.
boundProgram :: forall a. TyC a
  => (forall term. (Simplicity term, Primitive term) => term a ()) -> a -> Prog
boundProgram kernel = make
 where
  fingerprint = annotatedRoot (kernel :: AnnotatedRoot a ())
  descriptor = integerHash256 fingerprint `seq`
    BoundKernel kernel fingerprint (isClosed (kernel :: Closed a ()))
  make value = BoundProg (witness value >>> kernel) value descriptor

-- Interpret the entire source, including both branches. No witness or
-- disconnect is permitted inside a prepared kernel. Jet specifications cannot
-- contain either extension by the public Jet class contract.
newtype Closed a b = Closed { isClosed :: Bool }
both :: Closed a b -> Closed c d -> Closed e f
both (Closed a) (Closed b) = Closed (a && b)
instance Core Closed where
  iden = Closed True
  comp = both
  unit = Closed True
  injl (Closed a) = Closed a
  injr (Closed a) = Closed a
  match = both
  pair = both
  take (Closed a) = Closed a
  drop (Closed a) = Closed a
instance Assert Closed where
  assertl (Closed a) _ = Closed a
  assertr _ (Closed a) = Closed a
  fail _ = Closed True
instance Witness Closed where
  witness _ = Closed False
instance Delegate Closed where
  disconnect _ _ = Closed False
instance Primitive Closed where
  primitive _ = Closed True
instance Jet Closed where
  jet _ spec = spec
instance Simplicity Closed

-- | Whether a test vector is expected to be accepted or rejected.
data Expect = Accept | Reject deriving (Eq, Show)

-- | One test vector: a transaction environment, a witness, and an expected outcome.
--
-- The environment is a function of the program's CMR, because a taproot spend
-- commits to the CMR of the script being executed (exposed by the @script_cmr@ jet).
data Vector w = Vector
  { vecName    :: String
  , vecEnv     :: Hash256 -> Maybe PrimEnv
  , vecWitness :: w
  , vecExpect  :: Expect
  }

-- | Where a program's test vectors come from.
data VectorSource
  = Upstream String   -- ^ vectors copied from the spec (path under vendor-specs/)
  | Derived String    -- ^ vectors derived by us; the string says how
  deriving Show

-- | Corpus grouping, in GOAL.md priority order.
data Category
  = CovenantBip
  | BitcoinApp
  | PostQuantum
  | Stark
  | CrossChain
  | Eprint
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | A corpus program together with its test vectors.
data Entry = forall w. Entry
  { entryId       :: String        -- ^ stable identifier, e.g. @bip119-ctv-exact@
  , entryTitle    :: String
  , entrySpec     :: String        -- ^ the published spec this implements
  , entryCategory :: Category
  , entryVectorSource :: VectorSource
  , entryAssumptions :: [String]   -- ^ stated assumptions and bounds (max inputs, script lengths, ...)
  , entryProgram  :: w -> Prog
  , entryVectors  :: [Vector w]
  }
