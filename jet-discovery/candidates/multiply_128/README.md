# Candidate: `multiply_128` — 128x128 -> 256-bit multiplication

## Type signature
`(Word128, Word128) -> Word256`

## Specification
The library's `Simplicity.Programs.Arith.multiply word128`.

## Cost (ESTIMATE)
ESTIMATE: 4 x `Multiply64` = 0.288 WU.

## Generality
As for `div_mod_256`.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low to medium.

## Alternatives considered
`full_multiply_128` (with addends) would compose better.

## Corpus evidence
- `xchain-uniswap-v2-amount-out`: matched ×4 (static multiplicity); program cost 1410.366 WU → 25.288 WU with all candidates (55.8×).
- `ethsol-lending-liquidation`: matched ×1; program cost 138.722 WU → 122.918 WU (1.1×).

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
