-- | Complete bounded Bitcoin client statements. These are measured alongside
-- spending expressions but never acquire onchain feasibility from a virtual
-- primitive environment or a caller-provided clock/UTXO view.
module JetDiscovery.Corpus.BitcoinClients (entries) where
import JetDiscovery.Types(Entry)
import qualified JetDiscovery.Lib.NumericDlc as NumericDlc
import qualified JetDiscovery.Lib.Bolt12Invoice as Bolt12Invoice
import qualified JetDiscovery.Lib.ArkRefresh as ArkRefresh
import qualified JetDiscovery.Lib.CompactFilters as CompactFilters
entries :: IO[Entry]
entries=sequence[NumericDlc.entry,Bolt12Invoice.entry,ArkRefresh.entry,CompactFilters.entry]
