-- | The full corpus, in GOAL.md priority order.
-- Run from the jet-discovery directory: some entries read vectors from vendor-specs/.
module JetDiscovery.Corpus
  ( corpus
  ) where

import JetDiscovery.Types (Entry)
import qualified JetDiscovery.Corpus.Baseline as Baseline
import qualified JetDiscovery.Corpus.Bip348Csfs as Csfs
import qualified JetDiscovery.Corpus.Bip119Ctv as Ctv
import qualified JetDiscovery.Corpus.Bip446TemplateHash as TemplateHash

corpus :: IO [Entry]
corpus = concat <$> sequence
  [ pure Baseline.entries
  , Csfs.entries
  , Ctv.entries
  , TemplateHash.entries
  ]
