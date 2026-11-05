# Candidate: `m31_mul` — Mersenne-31 field multiplication

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`(Word32, Word32) -> Word32`

## Specification
For canonical M31 operands below `p = 2^31 - 1`, the arrow computes `a * b mod p`. Its typed inputs are two raw `Word32` values. The exact word operations are

```text
product = a * b                         # full 64-bit product
r = product & p
q = (product >> 31) mod 2^32
s = (q + r) mod 2^32
f = (s & p) + (s >> 31)
out = f - p if f >= p else f
```

For `a = b = 0xffffffff`, the arrow returns `2147483646`. Reducing the full product modulo `p` would return `1`. The truncated quotient and discarded addition carry are part of the raw-word specification. [Simplicity expression](../../src/JetDiscovery/Corpus/Stark.hs)

## Cost (ESTIMATE)
ESTIMATE: 2 x `FullMultiply32` = 0.174 WU.

## Generality
Circle STARKs (Stwo), Plonky3-style M31 systems.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low. C needs a full 32×32 product and the fixed folds. The u64/u128 oracle approach used for `fe_multiply` supplies a proof pattern. Equivalence covers the truncations and one final subtraction on every raw `Word32` pair. The independent field comparison in `test/Tests.hs` exercises canonical inputs. A consensus prototype needs a total word-level reference and raw boundary tests as well. A guarded canonical-only interface would define a different arrow and require new measurements.

## Alternatives considered
An M31 add/sub/inverse family; inversion is measured at about 700 WU in Simplicity.

## Corpus evidence
- `stark-m31-mul`: matched ×1 (static multiplicity); program cost 11.744 WU → 1.681 WU with all candidates (7.0×).
- `stark-m31-inv`: matched ×61 (static multiplicity); program cost 697.571 WU → 83.728 WU with all candidates (8.3×).
- `stark-fri-fold`: matched ×4 (static multiplicity); program cost 346.899 WU → 66.671 WU with all candidates (5.2×).
- `stark-fri-verifier` (complete circle-FRI verifier): matched ×192; program cost 9423.309 WU → 2742.125 WU with all candidates (3.4×; also qm31_mul ×18, sha256_pair ×104).

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
