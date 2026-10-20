# Field addition: scoped public and canonical source review

## Full public boundary

`fe_add_literal_local_spec` has precisely the existing `secp_jet_local_spec`
applied to original `f_simplicity_fe_add`, Word256-pair inputs, Word256 output
and `literal_fe_add` under CoreFunSem. Expanding that contract requires only
initial source metadata/alignment, representable cursors, encoded input cells
and a writable destination frame. It concludes the real public call returning
true, encoded output, prefix preservation, exact destination cursor and loads
outside the two modified output ranges. No helper execution, computed output,
final permission/freeing, extra libc model or impossible premise is added.

Both operands are arbitrary Word256 values, including values at/above the
field prime. The actual reader derives each normalized field; internal limb
and range premises are discharged by `normalized_add_reader_facts` and the
real two-reader execution, not exposed as public restrictions. Initial output
contents remain symbolic. Input consumption is 512 bits; output capacity is
256 bits. Shared frame-domain/evaluator admissibility remains a separate review.

## Original C lifecycle

The production C function has by-value source metadata, two field locals,
`read_fe(&a,&src)`, `read_fe(&b,&src)`, `secp256k1_fe_add(&a,&b)`,
`write_fe(dst,&a)` and return true. No extra normalizer is inserted.
`secp_fe_add_body` proves the exact generated body by reflexivity. Helper
symbol linkage is derived, not specified by a hardcoded block number.

`secp_fe_add_entry` derives the real 16/40/40-byte allocation sequence and
function_entry2. Preparation derives actual source-copy execution, freshness,
separation, Freeable storage and the read-only invariant. The two-reader lemma
derives both input slices from pair encoding, advancing the copied cursor by
512 and preserving the first field through the second read. The add/write
composition derives original helper/writer calls and literal output. The suffix
executes these actual calls and return; cleanup derives free_list of the exact
three-local environment. The lifecycle composes them into eval_funcall and
transports the output invariant/outside-memory relation through actual freeing.

## Literal canonical program

The Haskell catalog maps FeAdd to the field-add record at LibSecp256k1.hs:480:
add256, then carry-dependent expansion to `(one256, low)` or `(zero256, low)`,
then normalize512. `literal_fe_add` retains that term structure. The scribed
numeric modular sum is not substituted as its specification.

Canonical add prepends false carry to full_add. The shared formal add adapter
and literal division ports retain this, relating optimized support only by
proved semantic equalities. Normalize512 retains pairing with `(zero256, prime)`,
Word512 modulo and low-half projection. One256 is true followed by eight
left-padding levels: SingleV is identity, DoubleV pairs fill with recursive
padding, and low word1 is false. The new source gate checks that recursion,
the canonical branches, concrete widths, public C/body/local cleanup and final
contract. The reused recursive/foundational gates cover fill/zero, bit programs,
full addition, division, type/conversion/scribe and core notation mappings.

Public whole-chain kernel check 91932 passes with exit 0. Its printed context
matches exactly the 15 existing library axiom names, with all three unsafe
categories empty. Final theorem printing has six inherited Coq/CompCert
assumptions and no memcpy_model. All 26 proof modules/63 results are checked.
The new gate passes and rejects 52 in-memory mutations. Reused gates pass:
48 typed recursive ports/16 Haskell regions, literal division/field ports and
foundations; their 86+15+32 mutations also reject. One initial recursive-gate
invocation used the wrong reference directory and failed; the corrected call
uses the existing negate-review directory and passes without input changes.
