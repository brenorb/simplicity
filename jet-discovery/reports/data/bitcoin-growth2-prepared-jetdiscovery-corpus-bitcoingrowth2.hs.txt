-- | Later independently validated growth batches; kept separate while the
-- first BitcoinGrowth milestone is frozen for integration.
module JetDiscovery.Corpus.BitcoinGrowth2(entries) where
import JetDiscovery.Types(Entry)
import qualified JetDiscovery.Lib.SilentPayment as SilentPayment
import qualified JetDiscovery.Lib.ReserveProof as ReserveProof
entries :: IO[Entry]
entries=sequence[SilentPayment.entry,ReserveProof.entry]
