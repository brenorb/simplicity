# Candidate: `div_mod_512` — 512-bit division with remainder

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`(Word512, Word512) -> (Word512, Word512)`

## Specification
The library's `Simplicity.Programs.Arith.div_mod word512`.

## Cost (ESTIMATE)
ESTIMATE: 16 x `DivMod128_64` = 2.704 WU (schoolbook 512-by-256-bit division with 64-bit limbs; 4x the
`div_mod_256` estimate).

## Generality
Reduction of a 512-bit product modulo any 256-bit modulus: BIP 441 modular multiplication, scalar fields of non-native
curves (P-256's n, ed25519's l), hash-to-scalar reductions (ed25519 reduces SHA-512 output mod l).

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium: as `div_mod_256`, at twice the width.

## Alternatives considered
A `mod_mul_256 : ((Word256, Word256), Word256) -> Word256` jet (multiply then reduce) would fuse this with
`multiply_256` and is the operation every corpus use actually needs.

## Corpus evidence
- `bip441-bignum-modmul`: matched ×1 (static multiplicity); program cost 3808.209 WU → 15.269 WU with all candidates (249.4×).
- `xchain-p256-ecdsa`: matched ×3 (reductions mod n); `xchain-ed25519`: matched ×1 (SHA-512 output mod l).

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
