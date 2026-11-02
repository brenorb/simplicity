-- | The full corpus, in GOAL.md priority order.
module JetDiscovery.Corpus
  ( corpus
  ) where

import JetDiscovery.Types (Entry)
import qualified JetDiscovery.Corpus.Baseline as Baseline

corpus :: [Entry]
corpus = concat
  [ Baseline.entries
  ]
