# Candidate: `m31_mul` — Mersenne-31 field multiplication

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`(Word32, Word32) -> Word32`

## Specification
`JetDiscovery.Corpus.Stark.m31Mul`: `a * b mod (2^31 - 1)`.

## Cost (ESTIMATE)
ESTIMATE: 2 x `FullMultiply32` = 0.174 WU.

## Generality
Circle STARKs (Stwo), Plonky3-style M31 systems.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low. It is a 32x32 multiply and a Mersenne fold; the u64/u128 oracle approach used for `fe_multiply` applies.

## Alternatives considered
An M31 add/sub/inverse family; inversion is measured at about 700 WU in Simplicity.

## Corpus evidence
- `stark-m31-mul`: matched ×1 (static multiplicity); program cost 11.744 WU → 1.681 WU with all candidates (7.0×).
- `stark-m31-inv`: matched ×61 (static multiplicity); program cost 697.571 WU → 83.728 WU with all candidates (8.3×).
- `stark-fri-fold`: matched ×4 (static multiplicity); program cost 346.899 WU → 66.671 WU with all candidates (5.2×).
- `stark-fri-verifier` (complete circle-FRI verifier): matched ×192; program cost 9423.309 WU → 2742.125 WU with all candidates (3.4×; also qm31_mul ×18, sha256_pair ×104).

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
