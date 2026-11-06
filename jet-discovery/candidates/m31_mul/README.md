# Candidate: `m31_mul` — Mersenne-31 field multiplication

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
