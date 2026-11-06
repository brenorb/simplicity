# Candidate: `div_mod_512` — 512-bit division with remainder

## Type signature
`(Word512, Word512) -> (Word512, Word512)`

## Specification
The library's `Simplicity.Programs.Arith.div_mod word512` accepts two unrestricted unsigned 512-bit words. For a nonzero divisor it returns the exact quotient and remainder. Division by zero returns `(0, numerator)`. Both results retain the full width. [Simplicity expression](../../../Haskell/Core/Simplicity/Programs/Arith.hs)

## Cost (ESTIMATE)
The current overlay uses 16 × `DivMod128_64`, or **2.704 WU ESTIMATE**. The proxy models schoolbook 512-by-256-bit division with 64-bit limbs. The measured candidate accepts a full 512-bit divisor. The existing limb helper assumes a normalized divisor and a quotient that fits 64 bits. A C implementation of the wider arrow must handle divisor normalization and denormalization, quotient estimate corrections, the full input range, and the exact zero-divisor result. Benchmark those paths before using the proxy as a worst-path price.

## Generality
Reduction of a 512-bit product modulo any 256-bit modulus: BIP 441 modular multiplication, scalar fields of non-native
curves (P-256's n, ed25519's l), hash-to-scalar reductions (ed25519 reduces SHA-512 output mod l).

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium: as `div_mod_256`, at twice the width.

## Alternatives considered
A dedicated 512-by-256 division arrow would cover call sites whose divisor is known to fit 256 bits. A `mod_mul_256 : ((Word256, Word256), Word256) -> Word256` arrow would fuse multiplication and reduction at call sites that need the modular product. Each changes the ABI and requires its own proof, pricing, and matching evidence. The current full-width arrow also serves callers that consume a quotient.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
