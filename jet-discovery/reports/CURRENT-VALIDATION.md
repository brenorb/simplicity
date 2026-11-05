# Current validation checkpoint

The source milestone contains149 registered rows,145 distinct counting groups
and102 complete bounded spend/verifier groups. It does **not** meet the150-group
target. Old49-row cost/recommendation tables are historical and explicitly
withdrawn pending a complete fresh run. Vector-only evidence below supplies no
missing cost, profile, serialization or ablation numbers.

| Scope | Completed evidence | Remaining work |
| --- | --- | --- |
| Contract/Bitcoin expansion | All42 groups /202 vectors pass actual Bitcoin evaluation and same-jetted-CMR checks; [audit](CONTRACT-WITNESS-AUDIT.md) | Fresh shared cost/profile run |
| EVICT, BIP322, SPV receipt | All3 groups /27 vectors pass with actual TapTweak/TapLeaf funding outputs; [batch evidence](data/bitcoin-growth-batch1-provenance.json), [scope](BITCOIN-GROWTH.md) | Fresh shared cost/profile run |
| Silent payments and BIP127 reserve client | All9 native output-condition and7 client proof vectors pass with corrected raw outpoint bytes; actual C/Haskell wire checks and all9 legacy DER checks pass; [audit](OUTPOINT-BYTEORDER.md) | Fresh shared cost/profile run; old standard-wire compatibility claims withdrawn |
| Numeric DLC, BOLT12 and Ark clients | Complete15 numeric DLC,14 signed invoice and14 current Bark hArk certificate vectors pass; canonical wire/C checks cover all DLC/Ark environments; [DLC](NUMERIC-DLC.md), [BOLT12](BOLT12-INVOICE.md), [Ark](ARK-REFRESH-SCOPE.md) | Fresh metrics; no onchain-feasibility credit for client verifiers |
| BIP157/158 client | All10 official filter rows reconstructed and queried;52 actual source/boundary checks plus9 complete same-CMR vectors pass; [scope](COMPACT-FILTERS.md) | Fresh metrics; trusted checkpoint/completeness and false positives explicit |
| BIP152 client | All13 direct and13 prepared same-CMR vectors pass, plus12 independent wire/reference checks; [scope](COMPACT-BLOCK.md) | Fresh metrics; bounded two-transaction legacy block; full consensus/finality external |
| Private BIP47 client | All10 published notification/payment positives and9 actual corruption or re-signed payment negatives pass; [scope](PAYMENT-CODE.md) | Fresh shared metrics; offchain private interpreter only, budget feasibility inapplicable |
| PSBT finalizer/extractor | All 23 native client vectors pass; exact published mixed legacy/SegWit finalization and extraction, full inventory of 96 published binary records; [scope](PSBT-FINALIZER.md) | Fresh shared metrics; fixed authenticated session maps, no general PSBT parser or spend-budget claim |
| Delegated governance and quadratic funding | All 63 voting/treasury and 42 funded matching vectors pass; separate arithmetic/ancestry controls; [governance](SNAPSHOT-GOVERNOR.md), [funding](QUADRATIC-FUNDING-SCOPE.md) | Fresh shared metrics; bounded roster, clock and contribution domain explicit |
| Optimistic assertion bonds | All 42 native UMA lifecycle vectors, 41 rounding checks, and all 11 linked wire/C/Haskell/CSV positives pass; [scope](UMA-BOND.md) | Fresh shared metrics; fixed arbitrator and deadline race explicit |
| Funded Sablier cliff stream | All 38 native lifecycle vectors, 59 schedule checks and all 13 accepted wire/C/Haskell/ancestry controls pass; [scope](SABLIER-STREAM.md) | Fresh shared metrics; native signed cancellation valuation and freshness trust |
| Cumulative pull payments | All 28 native vectors pass, including genuine two-input payout control, lifetime rounding and actual continuation; [scope](CUMULATIVE-SPLITTER.md) | Fresh shared metrics; one native BTC lineage and immutable payees |
| Maker Clipper partial liquidation | All 51 native transaction vectors, 112 price and 248 fill checks, and 16 accepted wire/funding controls pass; [scope](CLIPPER-LIQUIDATION.md) | Fresh shared metrics; exact bounded whole-RAY quote and signed valuation, no current-time or Vat claim |
| Native mutual cover | All 63 policy, solvency, claim outcome and payout vectors pass; [scope](NEXUS-MUTUAL-NATIVE.md) | Fresh shared metrics; bounded fixed assessor, distinct accepted/draw/denied deposit treatment |
| Native Uniswap V2 fee-on pool | All 32 lifecycle vectors and 34 floor-square-root cases pass; [scope](UNISWAP-V2-POOL.md) | Fresh shared metrics; bounded two-class native coupon ledger and exact fee minting |
| StableSwap and weighted pools | All 23 three-class StableSwap and 18 two-class weighted lifecycle vectors pass; [evidence](NATIVE-PROTOCOLS-VALIDATION.md) | Fresh shared metrics; fixed native rates, rounding and liquidity bounds, no foreign asset-ledger equivalence |
| CoW batch settlement | All 20 complete native signed-order, settlement and accounting vectors pass; [evidence](NATIVE-PROTOCOLS-VALIDATION.md) | Fresh shared metrics; bounded two-order native claim ledger, no foreign interactions or expiry |
| Indexed loan and OCR report consumer | All 20 indexed lending and 11 fixed-config OCR vectors pass; independent canonical roots and exact source snapshots; [evidence](NATIVE-PROTOCOLS-VALIDATION.md) | Fresh shared metrics; native rate/height authority and OCR freshness limits explicit |
| Conditional positions | Complete29 native vectors pass plus independent focused layout/accounting review; [validation](NATIVE-PROTOCOLS-VALIDATION.md) | Fresh shared metrics; all six compact cohorts now pass separately |
| Native BIP32 wallet | All9 source/derivation/boundary controls and11 full native vectors pass; [scope](HD-WALLET.md) | Fresh shared metrics; unchanged hmac37 body with additive later helpers explicit |
| FairSwap file-sale escrow | All 24 actual native vectors pass under one canonical CMR, including the two-input payout regression; [scope and evidence](FAIRSWAP-NATIVE-SCOPE.md) | Fresh shared metrics; native CSV lower bounds and deadline races explicit |
| Bounded BLAKE3-256 | All 22 actual native vectors pass, including all 19 supported official unkeyed cases and three negatives; [scope](CRYPTO-FAMILIES.md) | One hash component, not a full application; fresh exact overlay match counts pending |
| BN254 Fp and Fp2 | All 12 actual vectors and complete two-entry costs; separate typed arrows and explicit dense arithmetic extrapolation [evidence](bn254-groth16.md) | Pre-final; no complete pairing verifier or budget claim |
| Full degree256 NTT | All15 full polynomial/direction/canonicality vectors pass; original source restored byte-for-byte after failed retention experiments; [restoration](data/ntt-original-restored.json) | Component only; complete final measurements run in its own process |
| New native contract adaptations | Eight complete groups /84 vectors pass: vault/share ledger, asynchronous claims, ascending/sealed auctions, Squads, Permit2, compressed asset transfer and13of19 guardian bridge; [validation](CONTRACT-GROWTH-VALIDATION.md) | Fresh shared cost/profile run; other drafts receive zero credit |
| Transport primitives | SipHash74, ChaCha20 block12 and Poly1305 MAC30 vectors pass; all named published sets covered; [scope](TRANSPORT-CRYPTO.md) | Three component families; fresh metrics |
| WebAuthn | All17 enrolled counter-wallet vectors pass the full P-256/assertion/state/payment expression; [scope](CRYPTO-FAMILIES.md) | Fresh metrics; enrollment/browser trust explicit |
| Poseidon2 and SHAKE256 | Full permutation14 and complete bounded sponge17 vectors pass, including published complete KAT sets; [scope](CRYPTO-FAMILIES.md) | Two component families; fresh metrics |
| LMS | Official RFC8554 certificate4 and transaction7 vectors pass | Fresh shared cost/profile run |
| XMSS | All7 transaction vectors pass | Fresh shared cost/profile run |
| SHRINCS | Stateful12 and stateless7 vectors pass | Fresh shared cost/profile run |
| FIPS205 SHA2-128s | Independent reference passes all28 supported official cases; Simplicity official KAT4 and native transaction7 pass; [completion](data/slh-standard-verification-status.json) | Fresh shared cost/profile run |
| Eprint relations | Expansion25 vectors, including FROST identity-commitment regressions, pass; six canonical-encoding control/attack pairs pass | Fresh shared full run; [detailed evidence](WITNESS-BINDING-AUDIT.md) |
| Ed25519 | All6 bound transaction-independent RFC/corruption vectors pass; [status](data/ed25519-bound-vectors-status.json) | Fresh shared cost/profile run |
| P-256 | All8 actual prepared-kernel vectors pass in3689.202seconds; RFC6979 positives and wrong message/key/scalar, r+n carry and canonical-key controls; [record](data/p256-prepared-vectors.json) | Fresh shared cost/profile run |
| TXHASH | All150 upstream successful selectors plus derived wrong-hash negative pass after canonical raw-outpoint repair, at one jetted CMR; [record](data/txhash-canonical-wire-vectors.json) | Fresh shared cost/profile run; malformed selector decoding remains host-only |
| Older settlement/guard repairs | DLC settlement11, Merkle-key4, Uniswap-v2 kernel10, P2MR7 and modular multiplication6 pass | All389 CTV,19 template/annex and32 upstream P2MR vectors also pass; fresh shared metrics remain |
| Full custom STARK | All8 full-size vectors and all analysis fields pass; native1,497,462.342WU; combined overlay252,144.216WU ESTIMATE; [complete snapshot](data/stark-full-pre-final-measurements.json) | Final frozen whole-corpus run; this pre-final binary has21 candidate frontends |
| Analysis | Full42-test suite passes816.99s; prepared-path3, candidate-recognition and canonical wire regressions pass; [record](data/harness-isolated-backend-current42.json) | Complete larger-corpus run remains |
| Upstream | Unchanged C suite98/98 and Haskell suite3252/3252 pass; default100 QuickCheck cases, no filter; [completion](data/upstream-validation-status.json) | No further upstream source changes are planned |

All listed pass claims have observed successful exit status or a separately
identified completed test in a preserved cohort log. Interrupted/heap-exhausted
diagnostics are retained as failures or incomplete work. They never count as
passing programs. The first multi-type mining fixture accidentally let its
unused widths erase; the corrected fixture forces both widths through equality
checks and passes. Earlier cost-regression cohorts preserve that fixture failure
while separately recording their successful counterfactual-cost checks.

The complete full-STARK resource diagnostic exited successfully in2313.146s;
it timed construction/cost/overlay/profile but did not print the resulting
values or assert its honest outcome, and omitted ablations. It is resource
evidence, not a substitute for the earlier honest-acceptance measurement or
the now-completed8-vector/complete analysis run. That later run exits0 in3839.262s and preserves every result in data/stark-full-pre-final-measurements.json; it remains pre-final whole-corpus evidence.

The earlier root BIP cohort is preserved in
data/root-corpus-repair-vectors-status.json. That driver captured only its
initial executable hash; later prefix binaries may have been rebuilt, which is
explicitly recorded rather than silently attributed to that initial hash. The earlier36-test
completion was observed in the tool result (1489.31s); its Cabal-generated log
was removed during reconfiguration before preservation. The current cohort
uses `tools/run_recorded.py`, which freezes the executable and captures output
and launch source hashes directly. The preserved39-test completion supersedes the older36-test observation;
the final frozen corpus still requires its complete shared run.
Unregistered growth drafts receive zero count credit. Source inventories and
their access gaps remain explicit in the separate coverage reports.
