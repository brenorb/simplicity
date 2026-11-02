# Candidate: `qm31_mul` — QM31 (degree-4 extension of M31) multiplication

## Type signature
`(((Word32, Word32), (Word32, Word32)), ((Word32, Word32), (Word32, Word32))) -> ((Word32, Word32), (Word32, Word32))`

## Specification
`JetDiscovery.Corpus.Stark.qm31Mul`, with u^2 = 2 + i and i^2 = -1.

## Cost (ESTIMATE)
ESTIMATE: `FeMultiply` = 0.407 WU (16 small-limb products and reductions).

## Generality
Circle STARK verification (FRI folding, DEEP quotients, OODS evaluations).

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low to medium: small integer arithmetic.

## Alternatives considered
Only `m31_mul`: QM31 then costs 16 jet calls plus plumbing.

## Corpus evidence
<!-- EVIDENCE -->
