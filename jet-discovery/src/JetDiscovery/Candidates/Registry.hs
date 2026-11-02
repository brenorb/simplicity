-- | The registry of candidate jets used by the what-if cost overlay
-- ("JetDiscovery.WhatIf").  Each candidate is documented in
-- candidates/<name>/README.md.
module JetDiscovery.Candidates.Registry
  ( candidates
  ) where

import JetDiscovery.JetSets (SomeCandidate)

candidates :: [SomeCandidate]
candidates = []
