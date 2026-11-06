# Candidate: `multiply_256` — 256x256 -> 512-bit multiplication

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
