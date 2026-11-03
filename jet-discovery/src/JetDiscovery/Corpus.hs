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
import qualified JetDiscovery.Corpus.CovenantMisc as CovenantMisc
import qualified JetDiscovery.Corpus.Apps as Apps
import qualified JetDiscovery.Corpus.Shrincs as Shrincs
import qualified JetDiscovery.Corpus.Hashes as Hashes
import qualified JetDiscovery.Corpus.Stark as Stark
import qualified JetDiscovery.Corpus.DeFi as DeFi
import qualified JetDiscovery.Corpus.MoreBips as MoreBips
import qualified JetDiscovery.Corpus.Ripemd as Ripemd
import qualified JetDiscovery.Corpus.Aggregate as Aggregate
import qualified JetDiscovery.Corpus.Bip346Txhash as Txhash
import qualified JetDiscovery.Corpus.ShrincsStateless as ShrincsStateless
import qualified JetDiscovery.Corpus.StarkFri as StarkFri
import qualified JetDiscovery.Corpus.P256 as P256
import qualified JetDiscovery.Corpus.Ed25519 as Ed25519
import qualified JetDiscovery.Corpus.Eprint as Eprint
import qualified JetDiscovery.Corpus.EthSol as EthSol

corpus :: IO [Entry]
corpus = concat <$> sequence
  [ pure Baseline.entries
  , Csfs.entries
  , Ctv.entries
  , TemplateHash.entries
  , Txhash.entries
  , pure CovenantMisc.entries
  , MoreBips.entries
  , pure Apps.entries
  , pure Ripemd.entries
  , pure Aggregate.entries
  , pure Shrincs.entries
  , pure ShrincsStateless.entries
  , pure Hashes.entries
  , pure P256.entries
  , pure Ed25519.entries
  , pure Stark.entries
  , pure StarkFri.entries
  , pure DeFi.entries
  , Eprint.entries
  , pure EthSol.entries
  ]
