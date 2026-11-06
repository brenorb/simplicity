# Candidate: `multiply_256` — 256x256 -> 512-bit multiplication

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: The regular wide product matches ten groups; the largest savings are concentrated in Ed25519 and P-256, which remain above their fixed-stack scenarios. Compare generic limb arithmetic against dedicated reductions before selecting a width.

Price: **1.152 WU (ESTIMATE)**. 16 x Multiply64: sixteen 64x64 products (schoolbook 256x256)

Matches in 10 of 157 registered rows: 10 matched DAG nodes across all branches, 35,689 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bip441-bignum-modmul | kernel | 3 | 1 | 3,838.308 | 3,607.668 | 230.640 | yes / yes at 4614 WU |
| xchain-p256-ecdsa | native_full_verifier | 8720 | 1 | 10,060,198.439 | 9,389,804.839 | 670,393.600 | no / no at 13272 WU |
| xchain-ed25519 | native_full_verifier | 17507 | 1 | 2,925,636.828 | 1,579,698.668 | 1,345,938.160 | no / no at 18820 WU |
| xchain-uniswap-v3-tick-math | kernel | 20 | 1 | 3,060.650 | 1,523.050 | 1,537.600 | yes / yes at 4597 WU |
| xchain-curve-stableswap-invariant | kernel | 608 | 1 | 514,052.014 | 467,308.974 | 46,743.040 | no / no at 5206 WU |
| xchain-fullmath-muldiv | kernel | 3 | 1 | 3,813.287 | 3,582.647 | 230.640 | yes / yes at 4588 WU |
| crypto-poly1305 | kernel | 96 | 1 | 22,775.359 | 15,394.879 | 7,380.480 | no / no at 3608 WU |
| app-webauthn-counter-wallet | native_full_spend | 8720 | 1 | 10,063,358.661 | 9,392,965.061 | 670,393.600 | no / no at 19725 WU |
| eprint-bn254-fp-multiply | kernel | 3 | 1 | 3,867.295 | 3,636.655 | 230.640 | yes / yes at 4627 WU |
| eprint-bn254-fp2-multiply | kernel | 9 | 1 | 11,821.680 | 11,129.760 | 691.920 | no / no at 4850 WU |

See the [complete matrix](../../reports/candidate-ranking.md#multiply_256) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`(Word256, Word256) -> Word512`

## Specification
The library's `Simplicity.Programs.Arith.multiply word256`.

## Cost (ESTIMATE)
ESTIMATE: 16 x `Multiply64` = 1.152 WU (schoolbook, sixteen 64x64 products).

## Generality
Modular arithmetic on 256-bit moduli: BIP 441's `OP_MUL` / `OP_MODMUL`-style big numbers, non-native curve fields
(P-256, ed25519) and their scalar fields, RSA-style modexp building blocks (Ethereum's modexp precompile).

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low to medium: the u128 oracles from the `fe_multiply` branch apply directly.

## Alternatives considered
- `full_multiply_256` (with addends) composes better into multi-limb code.
- Curve-specific field jets (`p256_fe_multiply`, `ed25519_fe_multiply`) subsume most uses on those curves.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
