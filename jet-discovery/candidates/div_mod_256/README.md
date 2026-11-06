# Candidate: `div_mod_256` — 256-bit division with remainder

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Strong**: The estimate crosses the fixed-stack scenario for bounded Uniswap V3 (22,235.642 to 9,708.540 WU against 12,694) and LMSR (17,404.636 to 16,082.774 WU against 16,379). It also materially reduces Balancer and Pendle. Benchmark exact full-width and normalized narrow division separately: the limb proxy is incomplete.

Price: **0.676 WU (ESTIMATE)**. 4 x DivMod128_64, a limb-throughput ESTIMATE; it does not model every step of unrestricted 256-by-256 division.

Matches in 7 of 157 registered rows: 7 matched DAG nodes across all branches, 148 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| xchain-uniswap-v3-tick-math | kernel | 1 | 1 | 3,060.650 | 1,738.788 | 1,321.862 | yes / yes at 4597 WU |
| app-weighted-pool-transition | native_full_spend | 82 | 1 | 152,067.689 | 25,884.091 | 126,183.598 | no / no at 14104 WU |
| app-proactive-market-maker-private-pool | native_full_spend | 9 | 1 | 114,255.531 | 102,358.773 | 11,896.758 | no / no at 16220 WU |
| app-lmsr-prediction-market | native_full_spend | 1 | 1 | 17,404.636 | 16,082.774 | 1,321.862 | no / yes at 16379 WU |
| app-pendle-term-market-transition | native_full_spend | 46 | 1 | 150,583.704 | 77,802.487 | 72,781.217 | no / no at 16869 WU |
| app-concentrated-pool-swap | native_full_spend | 8 | 1 | 22,235.642 | 9,708.540 | 12,527.102 | no / yes at 12694 WU |
| xchain-uniswap-v2-amount-out | kernel | 1 | 1 | 1,494.744 | 172.882 | 1,321.862 | yes / yes at 3283 WU |

See the [complete matrix](../../reports/candidate-ranking.md#div_mod_256) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`(Word256, Word256) -> (Word256, Word256)`

## Specification
The library's `Simplicity.Programs.Arith.div_mod word256` accepts two unrestricted unsigned 256-bit words. For a nonzero divisor it returns the exact quotient and remainder. Division by zero returns `(0, numerator)`. Both results retain the full width. [Simplicity expression](../../../Haskell/Core/Simplicity/Programs/Arith.hs)

## Cost (ESTIMATE)
The current overlay uses 4 × `DivMod128_64`, or **0.676 WU ESTIMATE**. This is a limb-operation proxy for dividing a 256-bit numerator. The existing 128-by-64 helper assumes a normalized divisor and a quotient that fits 64 bits. The candidate's full-width divisor also requires selecting and normalizing the active limbs, correcting quotient estimates as needed, and handling the zero case. A C benchmark must cover the full typed arrow before the proxy can serve as a worst-path price.

## Generality
Fixed-point and AMM arithmetic, big-number arithmetic (the Great Script Restoration's use cases), modular reductions for non-native fields.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium: u128 oracles exist (fe_multiply branch); division needs a quotient/remainder specification lemma.

## Alternatives considered
An unnormalized `div_mod_128_64`: the existing one requires a normalized divisor (`reports/mismatches.md` #3).

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
