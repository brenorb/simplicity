# Literal negation public boundary: scoped source review

## Final statement and input domain

The registered candidate theorem is
`C.jet_secp_negate_literal_contract.fe_negate_literal_local_spec`, with the
entire proposition `secp_jet_local_spec f_simplicity_fe_negate (Word 8) (Word 8)
(@literal_fe_negate Alg.CoreFunSem)`. No extra execution, arithmetic-result,
freeing, libc or impossible premise is introduced at that boundary.

Expanding the shared contract in `jet_secp_normalize_local.v` requires initial
source metadata/alignment, cursor representability, encoded input cells and a
writable destination frame. It concludes the real public Clight call returning
true, encoded specified output, preserved prefix, exact destination cursor and
loads outside the two modified ranges. The Word256 input is not restricted to
values below the field prime. Input/output-frame admissibility beyond those
explicit predicates remains a separate shared review obligation.

The internal sub-prime premise in `eval_negate_write_calls` is discharged by
`eval_negate_write_after_read_field`: it applies the actual reader's normalized
field representation and `canonical_normalized_field_range` to the original
Word256 value. `canonical_fe_negate_normalized_input` transports the result back
to negation of that original input. It is not an additional public domain
restriction. Initial destination contents are represented symbolically, not
assumed zero.

## Original C lifecycle and helper wiring

`jet_secp_negate_body.v` proves by reflexivity the complete generated body:
by-value source-frame copy, `read_fe`, in-place `secp256k1_fe_negate` with
magnitude one, `write_fe`, then return one. Its call adapter links the actual
helper symbol/function. No normalizer call is inserted into the public body.

`jet_secp_negate_lifecycle.v` derives both local allocations (16-byte source
frame and 40-byte field), source copy, fresh-local separation and Freeable
permissions through `secp_prepare_public_locals`. `exec_secp_fe_negate_rest_canonical`
derives the reader/helper/writer execution and final invariant. The lifecycle
then derives actual local freeing and stability of the output invariant and
outside-memory relation. These facts are conclusions of internal lemmas and
are discharged from initial state facts at the public boundary.

The wider-limb writer proofs execute the original complete `write_fe`. Its
numeric/byte bridge supports the unreduced limbs returned by negation; it does
not substitute an altered C writer or an assumed normalized output.

## Literal specification and semantic adapter

The final program is the literal scribed `(-1 mod fieldOrder)` factor, Word256
multiplication, Word512 modulo of `(zero256, fieldOrder)`, and low-half projection.
The integer `p - x` identity is a proved intermediate fact, not the program.

Division's optimized `Word.adder` calls are not claimed to be structurally
canonical. `canonical_add_word_matches_adder` proves the literal false-carry
full-adder equal for every width/input. `jet_literal_division_add.v` propagates
that equality through the actual typed approximation, correction loops,
recursive builder, div_mod and modulo ports. The final theorem uses those
literal ports and rewrites only along the formally proved equivalences.
Separate algebra-independent parametricity proofs retain the term structure.

The word-state conversion port and closed all-integer/all-depth bridge justify
the low-first Haskell conversion's `(hi,lo)` representation. Four source gates
check the reviewed catalog, recursive arithmetic, literal ports and foundational
type/conversion/scribe/notation regions; their 152 negative fixtures pass.
This is scoped source correspondence evidence, not a formal Haskell compiler.

## Acceptance still required

All 23 candidate proof modules freshly build, and the archived complete public
chain has an earlier independent kernel receipt. Candidate snapshot generation
completed successfully (27347); `SNAPSHOT-REVIEW.md` records unchanged old
records, 87 new results and 35 new definitions. Separate frozen full acceptance
is running as 57174. This review
does not itself promote candidate coverage or certify unrestricted evaluator
memory histories.
