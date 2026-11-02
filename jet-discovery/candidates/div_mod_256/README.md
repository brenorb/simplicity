# Candidate: `div_mod_256` — 256-bit division with remainder

## Type signature
`(Word256, Word256) -> (Word256, Word256)`

## Specification
The library's `Simplicity.Programs.Arith.div_mod word256`.

## Cost (ESTIMATE)
ESTIMATE: 4 x `DivMod128_64` = 0.338 WU.

## Generality
Fixed-point and AMM arithmetic, big-number arithmetic (the Great Script Restoration's use cases), modular reductions for non-native fields.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium: u128 oracles exist (fe_multiply branch); division needs a quotient/remainder specification lemma.

## Alternatives considered
An unnormalized `div_mod_128_64`: the existing one requires a normalized divisor (`reports/mismatches.md` #3).

## Corpus evidence
- `xchain-uniswap-v2-amount-out`: matched ×1 (static multiplicity); program cost 1410.366 WU → 25.288 WU with all candidates (55.8×).

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
