# Candidate: `multiply_128` — 128x128 -> 256-bit multiplication

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: This small carry proof has exact matches across 18 groups. The isolated estimate crosses the LMSR scenario by only 191.272 WU; larger savings in some pool predicates leave substantial residuals. Benchmark it against composition from existing Multiply64.

Price: **0.288 WU (ESTIMATE)**. 4 x Multiply64: four 64x64 products

Matches in 18 of 157 registered rows: 18 matched DAG nodes across all branches, 2,828 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bip441-bignum-modmul | kernel | 4 | 1 | 3,838.308 | 3,775.092 | 63.216 | yes / yes at 4614 WU |
| xchain-p256-ecdsa | native_full_verifier | 12 | 1 | 10,060,198.439 | 10,060,008.791 | 189.648 | no / no at 13272 WU |
| xchain-ed25519 | native_full_verifier | 4 | 1 | 2,925,636.828 | 2,925,573.612 | 63.216 | no / no at 18820 WU |
| xchain-uniswap-v3-tick-math | kernel | 2 | 1 | 3,060.650 | 3,029.042 | 31.608 | yes / yes at 4597 WU |
| xchain-curve-stableswap-invariant | kernel | 512 | 1 | 514,052.014 | 505,960.366 | 8,091.648 | no / no at 5206 WU |
| xchain-fullmath-muldiv | kernel | 4 | 1 | 3,813.287 | 3,750.071 | 63.216 | yes / yes at 4588 WU |
| app-webauthn-counter-wallet | native_full_spend | 12 | 1 | 10,063,358.661 | 10,063,169.013 | 189.648 | no / no at 19725 WU |
| app-stableswap-pool-transition | native_full_spend | 1536 | 1 | 218,376.473 | 194,101.529 | 24,274.944 | no / no at 11996 WU |
| app-weighted-pool-transition | native_full_spend | 288 | 1 | 152,067.689 | 147,516.137 | 4,551.552 | no / no at 14104 WU |
| app-proactive-market-maker-private-pool | native_full_spend | 35 | 1 | 114,255.531 | 113,702.391 | 553.140 | no / no at 16220 WU |
| app-lmsr-prediction-market | native_full_spend | 77 | 1 | 17,404.636 | 16,187.728 | 1,216.908 | no / yes at 16379 WU |
| app-pendle-term-market-transition | native_full_spend | 265 | 1 | 150,583.704 | 146,395.644 | 4,188.060 | no / no at 16869 WU |
| app-concentrated-pool-swap | native_full_spend | 48 | 1 | 22,235.642 | 21,477.050 | 758.592 | no / no at 12694 WU |
| app-lido-fifo-withdrawal-queue | native_full_spend | 6 | 1 | 2,288.682 | 2,193.858 | 94.824 | yes / yes at 6242 WU |
| eprint-bn254-fp-multiply | kernel | 4 | 1 | 3,867.295 | 3,804.079 | 63.216 | yes / yes at 4627 WU |
| eprint-bn254-fp2-multiply | kernel | 12 | 1 | 11,821.680 | 11,632.032 | 189.648 | no / no at 4850 WU |
| xchain-uniswap-v2-amount-out | kernel | 6 | 1 | 1,494.744 | 1,399.920 | 94.824 | yes / yes at 3283 WU |
| ethsol-lending-liquidation | native_full_spend | 1 | 1 | 138.722 | 122.918 | 15.804 | yes / yes at 1007 WU |

See the [complete matrix](../../reports/candidate-ranking.md#multiply_128) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`(Word128, Word128) -> Word256`

## Specification
The library's `Simplicity.Programs.Arith.multiply word128`.

## Cost (ESTIMATE)
ESTIMATE: 4 x `Multiply64` = 0.288 WU.

## Generality
As for `div_mod_256`.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low to medium. A C implementation needs four unsigned 64×64 full products, a fixed carry chain, and a 256-bit output writer. The read-only `feat/jet-equivalence` revision `771d41b98acc3750308a07c76405125bbc8439cd` contains `Coq/C/jet_multiply64_exec.v` and its contract snapshot. `eval_multiply64_composes` gives the local execution pattern for reading two 64-bit operands, using the u128 multiplication helper and writing the exact product. `Coq/C/jet_add64_wide_word.v` supplies the carry/payload relation. A new proof must reassemble the four products, establish carry bounds, and prove the complete frame and output order.

## Alternatives considered
`full_multiply_128` (with addends) would compose better.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
