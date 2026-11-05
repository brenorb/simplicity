# Native protocol batch: current outcomes

The three-outcome conditional-position application now has **29/29 actual guarded vectorsPASS**. Its predicate and input encoding are unchanged from the compact source; a separately generated canonical CMR is used only for offchain fixture signing. Exact whole-program and per-vector CMR checks remain active. The other five compact groups remain pending. No count or cost credit is assigned to unvalidated drafts or helper variants.

| Application group | Current result | Evidence |
|---|---|---|
| `app-conditional-position-partitions` | **29/29PASS, exit0**, 879.57s, peak RSS29456875520 bytes; actual canonical CMR `c7881650b7686ef1cc12d6954b048c7759efb9ad0387f60fff82fffd3bccc975` | `data/claim-full29-fixture32g.txt`, exact hashes in `data/claim-full29-freeze.json` |
| `app-interest-accruing-loan-rollover` | 20 application vectors pending; canonical-CMR extraction active | `data/loan-canonical-cmr32g.txt` |
| `app-batch-limit-order-settlement` | 20 application vectors pending | `tools/CheckNativeProtocols.hs` |
| `app-ocr-report-state-machine` | 11 application vectors pending | `tools/CheckNativeProtocols.hs` |
| `app-stableswap-pool-transition` | 23 application vectors pending | `tools/CheckNativeProtocols.hs` |
| `app-weighted-pool-transition` | 18 application vectors pending | `tools/CheckNativeProtocols.hs` |

The old and compact six-group runs exhausted16 GiB before vector1. Those failures remain in `data/native-protocols-vectors16g.txt` and `data/native-protocols-compact16g.txt`, with the representation change in `data/claim-ledger-compaction.json` and exact compact hashes in `data/native-protocols-freeze.json`. They are not passes.

The subsequent unchanged-predicate stage diagnostic passed at32 GiB:

| Stage | Elapsed | Result |
|---|---:|---|
| Actual canonical whole-program jetted CMR from typed dummy witness | 235.750205s | `c788...975` |
| Fixture signatures and complete5064-bit input | 2.388508s | constructed |
| Actual funding/continuation environment | 0.000003s | constructed |
| Pure-kernel jet substitution | 255.612554s | exact composed CMR equals actual canonical CMR |
| First full positive actual fastEval | 9.875491s | accepted |

`data/claim-stage-diagnostic32g.txt` retains all phases and resource data, including13458674528 bytes maximum live heap,30934597632 bytes peak RSS and2.134TB cumulative allocation. This identifies canonical/prepared construction as substantial work before any duplicate signing graph. The fixture optimization avoids a further whole-program compilation inside signature generation without changing the published predicate, static cost or native witness bytes. `data/claim-fixture-cmr-change.json` records the independently generated constant and old/new source hashes. A stale fixture fails the explicit whole-program CMR check and valid signature cases; the runtime never substitutes it for the actual measured CMR.

All29 application vectors exercise the actual bound witness, actual transaction environment and existing-jet Simplicity evaluator. They cover complete/subset split and inverse merge, ownership transfer, one oracle resolution, exact weighted redemption with floor rounding, both native claim issuances/transfers/maturity burns, forged actual old state, wrong actual full continuation, overlap/trivial partition, missing merge legs, inflation, wrong owner/oracle, repeated resolution/redemption, underbacking, funding shortfall and wrong payout script. Every supplied vector checks witness-invariant CMR through the prepared runner.

Metadata/comments were corrected after the successful run: before resolution all three outcome liabilities fit escrow; after resolution the exact weighted numerator liability fits `escrow * denominator`. The code already enforced that distinction and passed the weighted redemption vectors. Condition identity is implicit in the initialized UTXO lineage and six fixed subset-mask slots; the oracle signs the actual transaction containing the current funding outpoint and full state transition. No question/domain hash or exported position-ID bytes are computed. The tested pre-correction file is retained; only descriptive Entry assumptions/comments changed, with complete kernel/vector definitions unchanged. The metadata-only change record and current hash accompany the freeze. This is a complete bounded native adaptation; no foreign BN254 collection-ID, ERC1155 wire or global registry compatibility is claimed.


After the shared build, reproduce the complete registered application with
`jet-discovery verify app-conditional-position-partitions +RTS -N1 -M32G -RTS`
from the project directory. This main-runner route needs no unregistered
five-group draft modules. The final isolated full-corpus command additionally
measures every cost/profile/overlay/ablation field before strict aggregation.
