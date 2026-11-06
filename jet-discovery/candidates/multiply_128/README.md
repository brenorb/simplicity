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
Low to medium. A C implementation needs four unsigned 64×64 full products, a fixed carry chain, and a 256-bit output writer. The read-only `feat/jet-equivalence` revision `771d41b98acc3750308a07c76405125bbc8439cd` contains `Coq/C/jet_multiply64_exec.v` and its contract snapshot. `eval_multiply64_composes` gives the local execution pattern for reading two 64-bit operands, using the u128 multiplication helper and writing the exact product. `Coq/C/jet_add64_wide_word.v` supplies the carry/payload relation. A new proof must reassemble the four products, establish carry bounds, and prove the complete frame and output order.

## Alternatives considered
`full_multiply_128` (with addends) would compose better.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
