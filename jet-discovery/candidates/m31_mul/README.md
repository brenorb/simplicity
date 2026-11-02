# Candidate: `m31_mul` — Mersenne-31 field multiplication

## Type signature
`(Word32, Word32) -> Word32`

## Specification
`JetDiscovery.Corpus.Stark.m31Mul`: `a * b mod (2^31 - 1)`.

## Cost (ESTIMATE)
ESTIMATE: 2 x `FullMultiply32` = 0.088 WU.

## Generality
Circle STARKs (Stwo), Plonky3-style M31 systems.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low. It is a 32x32 multiply and a Mersenne fold; the u64/u128 oracle approach used for `fe_multiply` applies.

## Alternatives considered
An M31 add/sub/inverse family; inversion is measured at about 700 WU in Simplicity.

## Corpus evidence
<!-- EVIDENCE -->
