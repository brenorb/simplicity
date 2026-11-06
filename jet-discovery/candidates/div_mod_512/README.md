# Candidate: `div_mod_512` — 512-bit division with remainder

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: The bounded Curve invariant still costs 38,396.334 WU against its 5,206-WU scenario; the full StableSwap pool has no exact match. The only fit change is in the BN254 Fp2 kernel. Benchmark unrestricted and normalized division separately; the 512-by-256 price proxy is incomplete.

Price: **2.704 WU (ESTIMATE)**. 16 x DivMod128_64, a 512-by-256 proxy ESTIMATE; the exact prototype accepts a full 512-bit divisor.

Matches in 8 of 157 registered rows: 8 matched DAG nodes across all branches, 141 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bip441-bignum-modmul | kernel | 1 | 1 | 3,838.308 | 122.248 | 3,716.060 | yes / yes at 4614 WU |
| xchain-p256-ecdsa | native_full_verifier | 3 | 1 | 10,060,198.439 | 10,049,050.259 | 11,148.180 | no / no at 13272 WU |
| xchain-ed25519 | native_full_verifier | 1 | 1 | 2,925,636.828 | 2,921,920.768 | 3,716.060 | no / no at 18820 WU |
| xchain-curve-stableswap-invariant | kernel | 128 | 1 | 514,052.014 | 38,396.334 | 475,655.680 | no / no at 5206 WU |
| xchain-fullmath-muldiv | kernel | 1 | 1 | 3,813.287 | 97.227 | 3,716.060 | yes / yes at 4588 WU |
| app-webauthn-counter-wallet | native_full_spend | 3 | 1 | 10,063,358.661 | 10,052,210.481 | 11,148.180 | no / no at 19725 WU |
| eprint-bn254-fp-multiply | kernel | 1 | 1 | 3,867.295 | 151.235 | 3,716.060 | yes / yes at 4627 WU |
| eprint-bn254-fp2-multiply | kernel | 3 | 1 | 11,821.680 | 673.500 | 11,148.180 | no / yes at 4850 WU |

See the [complete matrix](../../reports/candidate-ranking.md#div_mod_512) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`(Word512, Word512) -> (Word512, Word512)`

## Specification
The library's `Simplicity.Programs.Arith.div_mod word512` accepts two unrestricted unsigned 512-bit words. For a nonzero divisor it returns the exact quotient and remainder. Division by zero returns `(0, numerator)`. Both results retain the full width. [Simplicity expression](../../../Haskell/Core/Simplicity/Programs/Arith.hs)

## Cost (ESTIMATE)
The current overlay uses 16 × `DivMod128_64`, or **2.704 WU ESTIMATE**. The proxy models schoolbook 512-by-256-bit division with 64-bit limbs. The measured candidate accepts a full 512-bit divisor. The existing limb helper assumes a normalized divisor and a quotient that fits 64 bits. A C implementation of the wider arrow must handle divisor normalization and denormalization, quotient estimate corrections, the full input range, and the exact zero-divisor result. Benchmark those paths before using the proxy as a worst-path price.

## Generality
Reduction of a 512-bit product modulo any 256-bit modulus: BIP 441 modular multiplication, scalar fields of non-native
curves (P-256's n, ed25519's l), hash-to-scalar reductions (ed25519 reduces SHA-512 output mod l).

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium: as `div_mod_256`, at twice the width.

## Alternatives considered
A dedicated 512-by-256 division arrow would cover call sites whose divisor is known to fit 256 bits. A `mod_mul_256 : ((Word256, Word256), Word256) -> Word256` arrow would fuse multiplication and reduction at call sites that need the modular product. Each changes the ABI and requires its own proof, pricing, and matching evidence. The current full-width arrow also serves callers that consume a quotient.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
