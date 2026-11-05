# Candidate: `multiply_256` — 256x256 -> 512-bit multiplication

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

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

## Corpus evidence
- `bip441-bignum-modmul`: matched ×1 (static multiplicity); program cost 3808.209 WU → 15.269 WU with all candidates (249.4×).
- `xchain-p256-ecdsa`: matched ×3 (inside the scalar-field multiplications mod n).

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
