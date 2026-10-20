# Field addition: complete compiled public candidate, not registered coverage

## Completed facts

- `eval_field_add_from_owned_region` derives the actual original
  `f_secp256k1_fe_add` call, final representation, unchanged region shape and
  outside-memory framing from two owned field representations. Initial field
  storage retains Freeable metadata for later public cleanup.
- `eval_field_add_with_values` derives all five actual output loads, each the
  machine sum of the corresponding input limbs, together with that real call
  and representation/framing. It assumes neither execution nor output.
- `add_value_unsigned` proves exact non-wrapping integer sums for the reader's
  52-bit limb bounds. `add_value_wide_bound` places them below the existing wide
  writer's `2^60` bound. Both final numeric results are closed.
- `eval_field_add_owned` composes the two-region execution from initial
  `fe_at` fields and Freeable storage, deriving the real call, result field,
  both locals' Freeable permissions and outside-memory framing. It assumes
  neither execution nor output. Its representation adapter is parameterized
  over the initial limb-variable index, rather than duplicating one-field
  proofs for the second operand.
- `field_add_values_sum` proves the actual five-limb output denotes the sum of
  the two initial field representations. Its final equality is closed. This is
  an implementation representation bridge, not a substitute canonical program.

Extract exact sources outside the repo with:

## Historical public composition boundary (now compiled)

The four-call composition now compiles as `eval_field_add_four_calls` from
canonical pair input and initial owned local storage, deriving all four actual
calls, literal output, all three locals' Freeable storage and outside-memory
framing. Its independent kernel check passes as 38991 (silent, without context
inventory). Statement sequencing and return, actual three-allocation entry and
exact free_list cleanup now compile too. Total compiled archive is twenty-three
modules/58 results, with twenty modules/48 already kernel-checked. Combined
rest/entry kernel check 59542 is live. Source-copy preparation and composition
of entry/body/return/free into the complete public contract remain open.

The actual public `simplicity_fe_add` body copies the by-value source, reads
two consecutive Word256 inputs into separate locals, invokes the original
in-place add helper on those locals, calls the original wide writer, and
returns true. The three-variable allocation/source-copy/entry/free lifecycle
must be derived. Existing one-field entry lemmas cannot simply be relabeled.

Canonical Haskell `fe_add` is `add256 >>> cond ((unit >>> one256) &&& iden)
((unit >>> zero256) &&& iden) >>> fe_normalize512`. Preserve that carry-expanded
Word512 combinator chain and its full Word256-pair input domain. This literal
port now exists, with closed parametricity proofs and a compiled numeric
interpretation. `add_writer_literal_output` compares the actual helper's limb
output with that literal program under intermediate normalized-reader facts;
it does not assume raw inputs below the field order. Its five-limb bounds and
two normalized values must still be derived from actual readers. Complete the
literal source gate and mutation tests, rather than substitute a numeric modular
addition as the specification. Derive the reader
normalization transport, writer output/prefix/cursor/framing and Freeable
storage for all locals. Only a complete checked public theorem, source review,
negative gates, reviewed snapshots and independent full acceptance can add
coverage. No registration is made here.
