# Current validation

The complete isolated cohort passed **2,698 of 2,698 vectors** across **157
registered programs**, **150 distinct counting groups** and **108 full
bounded spend or verifier groups**. The terminal manifest binds every exact
entry, vector log, checkpoint hash and strict aggregation to the same
source and frozen runner. It also retains both coordinator handoffs.
[Terminal manifest and run directory](data/isolated-final-157-lf/manifest.json)
[Verified local validation](data/final-validation.json)
[Derived publication manifest](data/recommendations-publication.json)

| Verified evidence | Coverage | Record |
| --- | ---: | --- |
| Complete corpus | 157 programs, 150 groups, 108 full groups, 2,698 passing vectors | [Per-program results](corpus-results.md) |
| Candidate scenarios | 23 frontends, 22 families, 3,611 isolated rows | [Ranked evidence](candidate-ranking.md) |
| Proposal and contract comparison | 335 source rows | [Coverage and costs](coverage-and-costs.md) |
| Local analysis harness | 45 passing tests, unfiltered | [Run record](data/harness-final45.json) and [output](data/harness-final45.txt) |
| Supplemental hash candidate references | 59 passing cases | [BLAKE2b](data/blake2b-candidate-reference-probe.txt), [SHA-512 and RIPEMD-160](data/hash-compression-reference-probe.txt) |
| Unchanged upstream suites | 98 C checks and 3,252 Haskell tests passed | [Run record and log hashes](data/upstream-validation-status.json) |
| Full STARK and stage costs | Complete custom proof verifier and checkpoint-derived stage analysis | [Verifier](FIBONACCI-STARK.md) and [stage evidence](data/stark-stage-final.json) |

The source rows include 24 open soft-fork BIPs, 10 unnumbered proposals,
40 TVL rows and 40 non-CEX TVL rows, 117 Ethereum block gas rows,
20 Ethereum UTC-day recipient rows, 64 Solana slot compute rows and 20
Soltop provider rows. Overlaps remain visible across source sets. Their
program links distinguish direct implementations, bounded adaptations,
proxies and unimplemented cases. [All source comparisons](coverage-and-costs.md)
[Period definitions and remaining access gaps](PERIOD-RANKINGS.md)

The program counts refer to the implemented bounded interfaces. The report
separates client verifiers, native spend conditions and components, and
labels hypothetical candidate costs as estimates. The custom STARK's
security and wire-interoperability boundaries, the BN254 pairing
extrapolation, and the ePrint full-text and implementation gaps remain
recorded. [Method and limits](METHOD.md#biases-and-limits)
[STARK scope](FIBONACCI-STARK.md)
[Groth16 estimate](bn254-groth16.md)
[ePrint scope](eprint-scan.md#remaining-review-and-implementation-gaps)

## Audit and reproduction

Run the default audit from `jet-discovery/` in the original measurement checkout.

```sh
python3 -B tools/check_final_evidence.py \
  --cohort reports/data/isolated-final-157-lf/manifest.json \
  --harness reports/data/harness-final45.json
```

At the signed report commit in a fresh checkout, add `--published-only`.
That audit checks the committed logs, report hashes and STARK stage
evidence. The original executable and other checkpoint byte checks belong
to the local audit. A fresh measurement builds the runner and creates a
new path-bound fingerprint. [Build, execution and publication commands](METHOD.md)

## Archived development evidence

The standalone and intermediate results below predate the terminal cohort.
Their historical follow-up notes describe the state at those checkpoints.
Use the terminal cohort above for current whole-corpus costs, serialization,
profiles, ablations and counts. The old 49-row results remain superseded.

| Scope | Completed development evidence | Notes at that checkpoint |
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
| DODO private pool and LMSR market | All 31 PMM and 38 LMSR lifecycle vectors pass; [DODO](DODO-VALIDATION.md), [LMSR](LMSR-MATH-VALIDATION.md) | Fresh shared metrics; fixed bounded reserve/claim, price and funding policies explicit |
| Pendle term market | All 34 complete native transaction vectors pass (18 accept, 16 reject); all 22 initial rate/trade controls pass; [scope](PENDLE-VALIDATION.md) | Fresh shared metrics; bounded authenticated time/index and actual BTC-backed native coupons |
| Finite Uniswap V3 pool | All 39 full native vectors (24 accept, 15 reject), 51 arithmetic and four targeted state binding controls pass; [scope](V3-NATIVE-VALIDATION.md) | Fresh shared metrics; finite tick map with exact Q96 crossings and Q128 fee checkpoints |
| Fixed-scale Curve Twocrypto | All 56 full native vectors pass (20 accept, 36 reject); 55 arithmetic comparisons pass; [scope and source branch proof](TWOCRYPTO-NATIVE.md) | Fresh shared metrics; fixed scale and exact supported Newton fallback, no moving EMA or ramp |
| Pump.fun virtual-reserve launch | All 48 current native vectors pass (13 accept, 35 reject), including exact sellout, permissionless migration and backed redemptions; [scope](PUMP-LAUNCH-NATIVE.md) | Fresh shared metrics; fixed native launch and migration handoff, no foreign mint or subsequent pool port |
| Lido FIFO withdrawal queue | All 31 bounded native vectors pass (15 accept, 16 reject), including source floor equality, two checkpoints, transfers and exact backed claims; [scope](LIDO-WITHDRAWAL-QUEUE.md) | Fresh shared metrics; pinned source payout logic, no foreign staking or timestamp attestation |
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
| Direct BIP347 OP_CAT | All 342 actual same-CMR vectors pass, including all 295 upstream value projections and 47 derived boundaries/negatives; [scope](BIP347-OP-CAT.md) | Standalone bounded component; fresh shared metrics; Script activation, stack underflow and policy are external |
| Vault recovery and aggregation bounds | Single-input and batch vault replay 10/10; additional guarded cross-input replay 18/18, including actual 16/17-input boundaries; [scope](VAULT-RECOVERY-BOUNDS.md) | Fresh shared metrics; one-input full-value recovery and enforced 16-input shared scan |
| Older settlement/guard repairs | DLC settlement11, Merkle-key4, Uniswap-v2 kernel10, P2MR7 and modular multiplication6 pass | All389 CTV,19 template/annex and32 upstream P2MR vectors also pass; fresh shared metrics remain |
| Full custom STARK | All8 full-size vectors and all analysis fields pass; native1,497,462.342WU; combined overlay252,144.216WU ESTIMATE; [complete snapshot](data/stark-full-pre-final-measurements.json) | Final frozen whole-corpus run; this pre-final binary has21 candidate frontends |
| Analysis | All 45 current tests passed unfiltered in 757.24s, including direct unpack equivalence, per-program mining output and the candidate saving with zero selected occurrences; [run record](data/harness-final45.json) | Fresh whole-corpus results and recommendations remain separate |
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
the full frozen corpus run was still pending at that checkpoint.
Unregistered growth drafts receive zero count credit. Source inventories and
their access gaps remain explicit in the separate coverage reports.
