-- | Static cost analysis for Bitcoin Simplicity expressions.
--
-- The library defines the 'Jet' instance of 'TermWeight' for Bitcoin in
-- @Simplicity.Bitcoin.StaticAnalysis.Cost@, a Backpack mixin module that the
-- Simplicity package does not re-export.  No exported module imports it, so we
-- restate the same two-line instance here (copied from
-- @Haskell/Indef/Simplicity/StaticAnalysis/Cost.hs@).
module JetDiscovery.Cost
  ( TermWeight(..)
  , milliWeigh
  , overhead
  ) where

import Simplicity.BitMachine.StaticAnalysis.Cost (TermWeight(..), milliWeigh, overhead)
import Simplicity.Bitcoin.Term (Jet(..), Simplicity)

instance Jet TermWeight where
  jet w _t = TermWeight $ overhead + w

instance Simplicity TermWeight where
