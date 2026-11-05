# Native protocol batch: current outcomes

All six compact native applications passed **121/121 actual guarded vectors**. Their predicates/input encoding are unchanged from the compact source; independently generated canonical CMRs are used only for offchain fixture signing. Exact whole-program and per-vector CMR checks remain active. No count or cost credit is assigned to unvalidated drafts or helper variants.

| Application group | Current result | Evidence |
|---|---|---|
| `app-conditional-position-partitions` | **29/29PASS, exit0**, 879.57s, peak RSS29456875520 bytes; actual canonical CMR `c7881650b7686ef1cc12d6954b048c7759efb9ad0387f60fff82fffd3bccc975` | `data/claim-full29-fixture32g.txt`, exact hashes in `data/claim-full29-freeze.json` |
| `app-interest-accruing-loan-rollover` | **20/20PASS, exit0**, 487.40s, peak RSS24217157632 bytes; exact canonical CMR `cdd787692459595d2da0b69e634bef5ea716042ef22b0ba53d6adb53dc9a5162` | `data/loan-full20-fixture32g.txt`, `data/loan-full20-freeze.json`, `data/loan-source-closure.json` |
| `app-batch-limit-order-settlement` | **20/20 PASS, exit 0**, 907.21 s, peak RSS 34,551,889,920 bytes; exact canonical CMR `469318e34bffe46c42f771aa62ee9ccd7b0da2800ea35405ff5431bbc21e11f3` | `data/batch-orders-full20-fixture32g.txt`, `data/batch-orders-full20-freeze.json`, `data/batch-orders-source-closure.json` |
| `app-ocr-report-state-machine` | **11/11 PASS, exit 0**, 333.41 s, peak RSS 10,887,577,600 bytes; exact canonical CMR `15035ac18ab2818a093ed0e3335d85c993b476ea66d13effb264199b0b593d28` | `data/ocr-full11-fixture32g.txt`, `data/ocr-full11-freeze.json`, `data/ocr-source-closure.json` |
| `app-stableswap-pool-transition` | **23/23 PASS, exit 0**, 1126.34 s, peak RSS 34,909,192,192 bytes; exact canonical CMR `d4d0a54c2f0a267534468b5d575cc34272811d2120b3ddaa950971e72a650fe2` | `data/stableswap-full23-fixture32g.txt`, `data/stableswap-full23-freeze.json`, `data/stableswap-source-closure.json` |
| `app-weighted-pool-transition` | **18/18 PASS, exit 0**, 919.11 s, peak RSS 34,908,864,512 bytes; exact canonical CMR `c1e2e389aa16c4d0c020ab4c33217701602304e191ac080739537fa49a0bef8c` | `data/weighted-pool-full18-fixture32g.txt`, `data/weighted-pool-full18-freeze.json`, `data/weighted-pool-source-closure.json` |

The normal Cabal build enables `RankNTypes` in `WeightedPool.hs` for its
polymorphic fixture constructor. The [parity record](data/weighted-pool-cabal-language-parity.json)
shows the exact one-line language pragma change and the frozen pre-registration
source. All predicates, fixture expressions and vectors are unchanged.

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


The loan vectors cover both account roles and actual funding of pool cash,
collateral and repayments; exact bounded index/reserve rounding; signed rate
and height; liquidation and terminal reserve/share withdrawals. The OCR
vectors check the canonical bounded ABI/context digest, distinct authorized
ECDSA signers, monotone epoch/round, transmitter and actual median payout. The
source-closure records identify the selected primary implementations and the
foreign state and hooks excluded from these bounded native applications.

After the shared build, reproduce each registered cohort with
`jet-discovery verify <exact-registered-id> +RTS -N1 -M32G -RTS` from the
project directory. The final isolated full-corpus command additionally
measures every cost/profile/overlay/ablation field before strict aggregation.
