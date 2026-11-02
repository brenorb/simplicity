{-# LANGUAGE ExistentialQuantification, RankNTypes #-}
-- | Corpus entry types.
--
-- A corpus program is a Bitcoin Simplicity program of type @term () ()@ that
-- is parameterised by its witness data.  The witness only changes the
-- 'witness' nodes of the program, never its commitment Merkle root (CMR) or
-- its static cost.
module JetDiscovery.Types
  ( Prog(..)
  , Expect(..)
  , Vector(..)
  , Category(..)
  , Entry(..)
  , VectorSource(..)
  ) where

import Simplicity.Digest (Hash256)
import Simplicity.Bitcoin.Primitive (PrimEnv)
import Simplicity.Bitcoin.Term (Simplicity, Primitive)

-- | A complete Bitcoin Simplicity program, polymorphic in its interpretation.
newtype Prog = Prog { unProg :: forall term. (Simplicity term, Primitive term) => term () () }

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
