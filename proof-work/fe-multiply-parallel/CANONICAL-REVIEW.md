# Canonical-fidelity review: `fe_multiply`, `fe_square`

Reviewed 2026-10-18 on `codex/fe-multiply-integration` against the pinned
original target (`git diff --quiet 91d89bac -- C Haskell Coq/Simplicity
':(exclude)C/test.c'` is clean). The mechanical part of this review is the
`Coq/mul-review/check-mul-wiring.py` gate (13 reviewed definitions and
propositions; `test-mul-wiring.py` rejects 41 source mutations), run by
`check-jets.sh`. This note records the human-readable correspondence.

## Pinned sources

| File | SHA-256 |
| --- | --- |
| `Haskell/Core/Simplicity/CoreJets.hs` | `90969fa951fc199d285d5b258758d2aa8490758f262e1b9973362fdfc35444dc` |
| `Haskell/Core/Simplicity/Programs/LibSecp256k1.hs` | `aa5ec6a57cef92f288f6b4b86180bfcaa80d9bc197a8f20879f14554f9a0842f` |
| `Haskell/Core/Simplicity/Programs/Arith.hs` | `728c56a6ba98fe7b9d205e0a36613c0db82b6468e840383fc3d9962d8b7ac2cf` |
| `Coq/Simplicity/Word.v` (upstream, unchanged) | `c6b03ec0c61802046450c7c94fb1258de3693003bb5db873c237f0ee82a7bf42` |
| `Coq/C/jet_multiply_spec.v` | `351c82aa8abed4dabd3982615ccd888a2c3f87ae1fee3da5db4892f54bc57532` |
| `Coq/C/jet_secp_negate_literal_contract.v` | `0b039ec88a1e1e37415be13e0df70e683a31ed3cf73998c2583ce3185bdb03d0` |
| `Coq/C/jet_parallel_fe_sqr_field.v` | `6188cc41578b710ba4e12af8d39c685166d148457896344ceb1fcf1c7af236fe` |
| `C/jets-secp256k1.c` | `13f9dbf66c162148a47abdd6f62c7dc852486efba3f8169531743031bfdb9592` |

## Catalog

`CoreJets.hs:405-406`: `FeSquare :: Secp256k1Jet Secp256k1.FE Secp256k1.FE`,
`FeMultiply :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE`;
`CoreJets.hs:800-801`: `specificationSecp256k1 FeSquare = Secp256k1.fe_square`,
`specificationSecp256k1 FeMultiply = Secp256k1.fe_multiply`. `FE` is `Word256`,
i.e. Coq `Word 8` (2^8 bits), so the Coq types are
`Ty.Prod (Word 8) (Word 8) -> Word 8` and `Word 8 -> Word 8`.

## Programs

| Haskell (`LibSecp256k1.hs`) | Coq literal port |
| --- | --- |
| `:484 fe_multiply = mul256 >>> fe_normalize512` | `literal_fe_multiply := @multiply_word_spec 8 term >>> @literal_fe_normalize512 term` |
| `:488 fe_square = iden &&& iden >>> fe_multiply` | `literal_fe_square := iden &&& iden >>> @literal_fe_multiply term` |
| `:383 mul256 = Arith.multiply word256` | `multiply_word_spec 8` (`Word 8` input halves, `Word (S 8)` = 512-bit result) |
| `Arith.hs:165 multiply w = iden &&& (unit >>> zero (DoubleV w)) >>> full_multiply w` | `multiply_word_spec n := comp (pair iden (comp unit (@zero (S n) term))) (@fullMultiplier n term)` |
| `Arith.hs:147-153 full_multiply` | upstream `Coq/Simplicity/Word.v:317-330 fullMultiplier` / `buildFullMultiplier` (same take/drop recursion; unchanged since 91d89bac) |
| `:407 fe_normalize512 = iden &&& (unit >>> zero256 &&& scribeFeOrder) >>> mod512 >>> ih` | `literal_fe_normalize512 := iden &&& (unit >>> (@Word.zero 8 term &&& Alg.scribe canonical_field_word)) >>> @literal_modulo_word_spec 9 term >>> I H` |
| `:403 mod512 = Arith.modulo word512`, `:351 scribeFeOrder = scribe256 LibSecp256k1.fieldOrder` | `literal_modulo_word_spec 9`, `canonical_field_word` (field order) |

`literal_fe_multiply` and `literal_fe_normalize512` are the field-negation
candidate's ports (its own review: main checkout `proof-work/fe-negate/CANONICAL-REVIEW.md`,
`check-literal-ports`/`check-recursive-ports`); this branch reuses them unchanged.
`literal_fe_square` is new; its only content is the pairing `iden &&& iden`
composed with `literal_fe_multiply`, exactly the Haskell record, and
`literal_fe_square_parametric` proves it parametric like the other literal ports.
`literal_fe_multiply_matches` relates the literal port to `canonical_fe_multiply`
(so `fe_multiply_local_spec` is also stated for the canonical form).

Numeric meaning (supporting lemmas, not substitutes for the program):
`literal_fe_multiply_numeric` / `literal_fe_square_numeric` give
`(a * b) mod p` / `(a * a) mod p` through `multiply_word_spec_numeric` and
`canonical_fe_normalize512_numeric`; the C side is related by these values.

## Original C

`C/jets-secp256k1.c`: `simplicity_fe_multiply` reads `a`, `b`, calls
`secp256k1_fe_mul(&a, &a, &b)` (aliasing `r = a`), writes `a`;
`simplicity_fe_square` reads `a`, calls `secp256k1_fe_sqr(&a, &a)`, writes `a`;
both return `true`. The gate checks these bodies and the generated-AST
statement shapes (`secp_fe_mul_rest`, `secp_fe_sqr_rest`, the helper call
statements and the body equalities `secp_fe_mul_body`, `secp_fe_sqr_body`).

## Verdict

No mismatch found. The registered contracts are
`secp_jet_local_spec f_simplicity_fe_multiply (Ty.Prod (Word 8) (Word 8)) (Word 8) (@literal_fe_multiply Alg.CoreFunSem)`
and `secp_jet_local_spec f_simplicity_fe_square (Word 8) (Word 8) (@literal_fe_square Alg.CoreFunSem)`.
