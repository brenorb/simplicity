# Complete original public C field multiplication

`FieldPublic.Public.eval_original_public_field_multiply` proves an actual
`Clight2.eval_funcall` of the unchanged `f_simplicity_fe_multiply`, returning
`Vint Int.one` with the encoded raw-input product modulo the field prime,
the existing full `finv` output/cursor contract, and outside-frame memory
framing. Both Word256 inputs are unrestricted.

Only the original source/output frame, encoded input and cursor/capacity
facts are premises. There are no caller-local storage, intermediate
representation, limb-bound, helper-execution or output premises. The proof
derives all three allocations in their actual order (source copy, `a`, `b`),
the by-value source-frame copy in that three-local environment, both readers,
the in-place multiplier, the original writer, return conversion to Boolean,
and actual `Mem.free_list` cleanup of all three locals.

The new environment's `blocks_of_env` was computed and proved exactly as
`[(bl,0,16); (ba,0,40); (bb,0,40)]`; no free-list order or symbol block number
is assumed. Freshness is relative to the original memory when composing the
allocation/copy/body/free frame predicates, so newly allocated blocks cannot
be incorrectly treated as old memory.

This is still a numeric intermediate result, **not yet the public literal
Simplicity-specification theorem**. `input_product_word` remains the named
bridge from the checked input packet, not a replacement specification.
Connect the original literal multiply/normalize512 program and retain the
full public frame contract before any registry or acceptance update.

## Verification

Five sources, sixteen results, ten definitions. Exact dependency profile:
six closed results, two memory-framing results with four inherited classical
dependencies, eight execution results with the six inherited Coq/CompCert
dependencies. No new axioms or external model is added.

Next reuse the existing `literal_fe_multiply` term and its canonical
multiply/normalize512 semantic bridges, after source-bound verification and
the existing literal/recursive/foundation correspondence gates. Prove that
`input_product_word x y` equals that literal program's result, then specialize
the complete C theorem to the existing `secp_jet_local_spec`. Do not define
a new numeric specification or alter the original code/domain/API to close
that final boundary.

Production C, original specifications, API, generation settings, main proof
sources, registry and unrelated staged patch are unchanged. Public coverage
added: zero.
