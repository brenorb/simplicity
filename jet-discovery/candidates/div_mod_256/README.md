# Candidate: `div_mod_256` — 256-bit division with remainder

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`(Word256, Word256) -> (Word256, Word256)`

## Specification
The library's `Simplicity.Programs.Arith.div_mod word256` accepts two unrestricted unsigned 256-bit words. For a nonzero divisor it returns the exact quotient and remainder. Division by zero returns `(0, numerator)`. Both results retain the full width. [Simplicity expression](../../../Haskell/Core/Simplicity/Programs/Arith.hs)

## Cost (ESTIMATE)
The current overlay uses 4 × `DivMod128_64`, or **0.676 WU ESTIMATE**. This is a limb-operation proxy for dividing a 256-bit numerator. The existing 128-by-64 helper assumes a normalized divisor and a quotient that fits 64 bits. The candidate's full-width divisor also requires selecting and normalizing the active limbs, correcting quotient estimates as needed, and handling the zero case. A C benchmark must cover the full typed arrow before the proxy can serve as a worst-path price.

## Generality
Fixed-point and AMM arithmetic, big-number arithmetic (the Great Script Restoration's use cases), modular reductions for non-native fields.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium: u128 oracles exist (fe_multiply branch); division needs a quotient/remainder specification lemma.

## Alternatives considered
An unnormalized `div_mod_128_64`: the existing one requires a normalized divisor (`reports/mismatches.md` #3).

## Corpus evidence
- `xchain-uniswap-v2-amount-out`: matched ×1 (static multiplicity); program cost 1410.366 WU → 25.288 WU with all candidates (55.8×).

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
