# DODO bounded native private-pool validation

The exact fixed-k0.1 arithmetic helpers have **26/26 actual Simplicity vectors passing**, and the complete PMM regime pricing helper passed **14/14**. Both use same-program CMR checks and independent Integer translations. The complete bounded private-pool application also passed **31/31 actual guarded vectors**, including 21 expected accepts and 10 expected rejections. Registry integration and static cost measurement are separate.

| Stage | Current outcome | Evidence |
|---|---|---|
| Integer square roots used by target/trade | 116/116PASS, 3 GiB cap | `data/bounded-sqrt-vectors.txt` |
| DODO target, k0.1 | 8/8PASS, exit0, 43.22s, peak RSS3033759744 bytes | `data/dodo-target3g.txt` |
| DODO quadratic trade, k0.1 | 11/11PASS, including altered output/zero target/zero reserve | `data/dodo-trade-integral3g.txt` |
| DODO integral, k0.1 | 7/7PASS, including altered output/reversed interval; combined trade+integral27.33s, peak RSS2349088768 bytes | `data/dodo-trade-integral3g.txt` |
| All three PMM regimes, target adjustment and crossing | **14/14 PASS**, exit 0, 74.06 s, peak RSS 16,500,703,232 bytes under the16 GiB cap. Earlier3 GiB attempt exhausted heap before vector1 | `data/dodo-pmm-regimes16g.txt`, `data/dodo-pmm-regimes3g.txt` |
| Complete native DPP lifecycle, 31 vectors | **31/31 PASS**, exit 0, 821.06 s at the32 GiB heap cap, maximum RSS 32,415,383,552 bytes. Exact canonical fixture parity and guarded per-vector execution | `data/dodo-pool-canonical-cmr32g.txt`, `data/dodo-pool-full31-fixture32g.txt`, `data/dodo-pool-full31-freeze.json` |

Sources are pinned at DODOEX/contractV2 `2f1bcdac7ef1beee7599a756e2eed26732c2536d`, selected `DODOMath.sol`, `PMMPricing.sol`, and the DPP trader/storage/admin/vault path. Existing source provenance and `vendor-specs/contract-growth/dodo-private-pool-provenance.json` record the exact files. Retained Solidity is inert specification data; no downloaded code is executed. The selected path is the private pool, not DVM. In particular, the implementation retains all ONE/ABOVE_ONE/BELOW_ONE regimes, adjusted targets, integral precision caps, exact crossings and the DPP trader's direction-specific conditional storage of new targets.

The native profile has fixed k0.1 and zero LP/maintainer fees, both supported source configuration choices. It commits complete ownership, total supplies and reserves for two BTC-backed coupon classes, with different maturity heights. Owner0 funds, withdraws or resets the private pool using existing owned coupons; traders exchange owned coupons against committed reserves. No synthetic LP shares or global ERC20 supply is assumed. Every branch checks actual current input0, actual funding or exact payments, and the same executable continuation committing the entire new ledger. Price resets are authenticated owner configuration, not proof of external current-price freshness.

Helper formulas preserve the source's nested integer floors/ceiling and full square roots. Arithmetic uses checked128-bit intermediates and256-bit products/division where required. The application bounds reserves to1..1e9, stored targets to1..4e9, price to0.5..2 at1e18 precision and disallows one-sided empty pools. The defined empty state has both reserves/targets/R zero. Nonzero-output trade bounds and fixed actors are explicit native restrictions. Source callbacks, flash execution and arbitrary external admin modules are outside this profile.

The typed PMM helper stages both adjusted targets, then one quote, before producing receipt/new targets/newR. The application stages that one pure quote alongside the one aggregate witness. No repeated witness expression is used to assert a logical value and separately consume it. The exact source snapshots and fixture-only change distinguish helper tests from complete application execution.


The independent typed-dummy commitment is `fc1be04a86d81a9fafeab4eaa2b968d35fc2004ccc9799a6dbbbec312a4a057f`. The full run checks the actual canonical whole-program CMR against it before checking each vector. Precomputing that fixture commitment avoids compiling a second simultaneous signing graph and does not alter the predicate or witness encoding. The [source closure](data/dodo-pool-source-closure.json) verifies six selected source files, retained license evidence, and the exact program/driver hashes. This is one application family; the integer square root and PMM helpers are components.
