# Candidate: `multiply_128` — 128x128 -> 256-bit multiplication

## Type signature
`(Word128, Word128) -> Word256`

## Specification
The library's `Simplicity.Programs.Arith.multiply word128`.

## Cost (ESTIMATE)
ESTIMATE: 4 x `Multiply64` = 0.145 WU.

## Generality
As for `div_mod_256`.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low to medium.

## Alternatives considered
`full_multiply_128` (with addends) would compose better.

## Corpus evidence
<!-- EVIDENCE -->
