# Candidate: `qm31_mul` — QM31 (degree-4 extension of M31) multiplication

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`(((Word32, Word32), (Word32, Word32)), ((Word32, Word32), (Word32, Word32))) -> ((Word32, Word32), (Word32, Word32))`

## Specification
For canonical M31 coefficients, the arrow multiplies in the tower with `i^2 = -1` and `u^2 = 2 + i`. A value `(a,b)` represents `a + bu`, and each pair `(x,y)` in a coefficient represents `x + yi`.

For raw words, use the exact [M31 word multiplication](../m31_mul/README.md) at the base. Base addition wraps modulo `2^32` and then conditionally subtracts `p` once. Base subtraction returns the wrapped difference and adds `p` modulo `2^32` on borrow. With those operations, the reference evaluates the fixed tower formula below. Addition on a pair acts on its corresponding coefficients.

```text
cmul((x,y),(z,w)) = (sub(mul(x,z),mul(y,w)), add(mul(x,w),mul(y,z)))
timesR((x,y))     = (sub(add(x,x),y), add(x,add(y,y)))
qmul((a,b),(c,d))  = (cmul(a,c) + timesR(cmul(b,d)), cmul(a,d) + cmul(b,c))
```

Squaring `((0xffffffff,0),(0,0))` yields `((2147483646,0),(0,0))`. Interpreting the input as a field element after first reducing the raw coefficient modulo `p` would give `((1,0),(0,0))`. [Simplicity expression](../../src/JetDiscovery/Corpus/Stark.hs)

## Cost (ESTIMATE)
The current overlay uses `FeMultiply` at **0.813 WU ESTIMATE** as an implementation analogue. The exact expression contains 16 base-field products plus tower additions and subtractions. This proxy differs from the cost of composing 16 calls to the independently priced `m31_mul` candidate. C benchmarking should compare both constructions.

## Generality
Circle STARK verification (FRI folding, DEEP quotients, OODS evaluations).

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low to medium. C can use 16 unsigned 32×32 full products, Mersenne folds, and fixed add/subtract steps for the two extension levels. At read-only `feat/jet-equivalence` revision `771d41b98acc3750308a07c76405125bbc8439cd`, `Coq/C/jet_multiply_wide_exec.v` and its contract snapshot cover the 32-bit multiply-to-64-bit execution pattern. `Coq/C/jet_add32_wide_word.v` covers the carry and payload relation for addition. The new obligations are the M31 reduction, the coefficient order and reduction identities for both extension levels, and the exact frame and output layout. The independent field comparison uses canonical M31 coefficients. A jet proof must also match the arrow on every raw Word32 input accepted by its type.

## Alternatives considered
Only `m31_mul`: QM31 then costs 16 jet calls plus plumbing.

## Corpus evidence
- `stark-qm31-mul`: matched ×1 (static multiplicity); program cost 245.781 WU → 5.805 WU with all candidates (42.3×).
- `stark-fri-fold`: matched ×1 (static multiplicity); program cost 346.899 WU → 66.671 WU with all candidates (5.2×).
- `stark-fri-verifier`: matched ×18 (static multiplicity); program cost 9423.309 WU → 2742.125 WU with all candidates (3.4×).

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
