# Candidate: `m31_mul` — Mersenne-31 field multiplication

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Strong**: The full STARK accounts for most savings, and the isolated M31 overlay does not make it fit the fixed-stack scenario. Benchmark this small reusable primitive alongside QM31 because the proof burden is smaller; compare the overlapping savings and exact raw-word contract.

Price: **0.174 WU (ESTIMATE)**. 2 x FullMultiply32: one 32x32 multiply plus a Mersenne fold of similar cost

Matches in 5 of 157 registered rows: 5 matched DAG nodes across all branches, 81,154 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| stark-m31-mul | kernel | 1 | 1 | 11.744 | 1.681 | 10.063 | yes / yes at 233 WU |
| stark-m31-inv | kernel | 61 | 1 | 697.571 | 83.728 | 613.843 | no / yes at 319 WU |
| stark-qm31-mul | kernel | 16 | 1 | 245.781 | 84.773 | 161.008 | yes / yes at 387 WU |
| stark-fri-fold | kernel | 20 | 1 | 346.899 | 145.639 | 201.260 | yes / yes at 487 WU |
| stark-fibonacci-full | native_full_verifier | 81056 | 1 | 1,497,462.342 | 681,795.814 | 815,666.528 | no / no at 286745 WU |

See the [complete matrix](../../reports/candidate-ranking.md#m31_mul) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

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
An M31 add, subtract, and inverse family would cover other field operations.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
