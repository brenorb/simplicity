# Vault recovery and cross-input amount bounds

The bounded single-vault leaf and both cross-input amount components now
enforce their declared funding limits. These fixes affect the local study
programs. They change no Bitcoin Simplicity primitives or costs.

The historical [BIP 345 recovery specification](../vendor-specs/bips/bip-0345.mediawiki)
requires the recovery output to include the vault's full input amount. The
single-input native [vault leaf](../src/JetDiscovery/Corpus/Apps.hs)
previously checked only output 0's script. Immediate recovery now requires
one actual transaction input and checks that output 0 pays its full value
to the expected script. This leaves no fee from the vault input in this
profile; relay policy and fee sponsorship are outside it. The withdrawal
branch still enforces its native template and relative delay. Both paths
now use funding P2TR scripts constructed from the actual program CMR and
the vault's committed template. The same leaf accepts full-value recovery
and rejects the wrong destination, a one-satoshi shortfall and two vault
inputs claiming one output. All seven vectors pass.
[Run record](data/vault-recovery-current10.json) and
[actual output](data/vault-recovery-current10.txt).

The [shared cross-input sum](../src/JetDiscovery/Corpus/Aggregate.hs)
previously scanned indices 0–15 but did not check the actual input count.
Both the CCV amount and batched vault recovery components accepted a
transaction with 17 matching 1,000-satoshi inputs and a 16,000-satoshi
output. This held when evaluating from either the first or last input.
The sum now verifies the 16-input limit before scanning. It preserves
the matching-script and overflow checks. It accepts a valid 16-input
boundary, excludes unrelated inputs from the sum, and rejects all
17-input cases even if the output is fully funded. The old and guarded
18-vector runs each include the original registered vectors. Both logs
record the exact CMRs and outcomes.
[Legacy run](data/aggregate-input-bound-legacy.txt),
[guarded run](data/aggregate-input-bound-guarded.txt) and
[provenance](data/aggregate-input-bound-provenance.json).

Batched recovery still groups by equal script and targets output 0.
The repair does not emulate BIP 345's general Script deferred-check
machinery or complete the omitted BIP 443 modes.
