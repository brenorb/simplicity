# Continue from the complete original scalar_mul call

Last verified declaration:
`LifeC.jet_secp_scalar_mul_caller_observed.eval_scalar_mul_caller_inplace_observed`.
All three proof modules, both audit drivers and the independent kernel check
passed after the final rebuild. No open proof remains in this archive. The
earlier function-boundary task in `../scalar-mul-caller/CONTINUATION.md` is now
complete for `[a,a,b]`; its public/square tasks remain open.

## Next: public multiplication composition

Keep the intended root visible: complete original
`simplicity_scalar_multiply` execution against the **literal**
`canonical_scalar_multiply` under general input/output frame contracts. Do not
substitute a numerical modulo specification for that root.

The generated wrapper has two scalar locals and the by-value source frame:
copy source, read/normalize a, read/normalize b, call `scalar_mul(a,a,b)`,
write a, return true, free the actual outer locals. The new internal root
discharges only its scalar_mul segment.

1. Reuse the two existing scalar reader executions with actual source cursor
   advancement and normalized machine words. Preserve a while reading b,
   using the **current** memory, then build `scalar_mul_caller_inputs` from
   those loads and actual owned local regions. Construct rho from the eight
   returned limbs; do not assume the post-reader representation.
2. Instantiate `eval_scalar_mul_caller_inplace_observed`. Its four actual
   post-free `Vlong` loads and surviving ownership form the writer adapter's
   input. Retain numeric carrier bounds and any normalization facts required
   by the writer; equality of a weighted value alone may not establish them.
3. Reuse the original scalar writer. Prove its representation from those
   current-memory loads, preserve the external frame invariants, and derive
   the original return/outer free-list rather than assuming cleanup.
4. Connect the reader normalization and product/modulo identity to the existing
   literal `canonical_scalar_multiply` semantics and parametricity bridge.
   Preserve both raw inputs for this final relation. Prove output encoding,
   cursor advancement and permitted memory changes under the original frame
   contract.
5. Rebuild the whole chain, inspect full root types/definitions/dependencies,
   and independently kernel-check it before isolated registry promotion and
   integrated acceptance. A helper milestone must not increase coverage.

Useful modules in the immutable base
`/tmp/jet-scalar-integration.XAMDsw/Coq/C`:

- `jet_secp_scalar_reader_lifecycle.v`, especially
  `eval_scalar_reader_numeric_owned`;
- `jet_secp_scalar_writer_exec.v`, `jet_secp_scalar_writer_numeric.v`,
  `jet_secp_scalar_writer_storage.v`, `jet_secp_scalar_read_write.v`;
- `jet_secp_canonical_scalar.v`, `jet_secp_canonical_scalar_negate.v` and
  `jet_secp_canonical_scalar_negate_parametric.v`. The latter naming predates
  this milestone; inspect their actual multiplication definitions/lemmas.

There is no `jet_secp_scalar_writer_lifecycle.v` in that base. The pending
scalar-add candidate `/tmp/jet-scalar-add-integration.RxsuOy/Coq/C` has reusable
reader/environment/body/literal-owned/local decomposition. Read its exact
contracts before adapting it; do not mutate its frozen acceptance evidence.

## Square is still a separate input-alias proof

The square wrapper calls `scalar_mul(a,a,a)`. The current two-owned-input
representation implies operand separation, so it cannot be instantiated by
duplicating a's owned region. Support for destination alias `r=a` does not
establish input alias `a=b`.

Prove a fresh same-input product run with layout `[l,a]` and both input
pointers equal. Reuse the checked column arithmetic through an explicit
source/denotation map duplicating the four input limbs in rho. Then compose
reduction and the actual caller allocation/free boundary for this layout.
Retain the literal square program `iden &&& iden >>> scalar_multiply` at the
public root. There is no separate scalar_sqr C helper to invent.

## Avoid repeating diagnosed failures

- Representation layouts use `block` (an alias of positive); a generic
  `In_nth` experiment inferred a differently folded product type and a rewrite
  failed although the pretty-printed terms looked equal. `Set Printing All`
  exposed this. The actual input-validity lemma needs only the exact two-entry
  layout; that concrete decomposition proved it directly.
- After inversion, concrete u64 cells may be expanded, preventing inference
  of xs/ys. Supply xs, ys, rho/rho', permissions and ownership explicitly to
  `region_u64_transport`.
- `rep_prefix`'s layout-suffix argument is named `βN`, not `betaN`.
- Import `Clightdefs` explicitly for `tulong` notation.
- Whole symbolic product/reduction normalization is expensive. The layout
  independence lemma closes with `unfold final_output_value. f_equal.`
  without expanding the arithmetic.
- The observation module locally marks the symbolic product/reduction
  intermediates opaque after their definitions. This prevents elaboration of
  a single region load from expanding the entire product. Supply the exact
  region to `region_load`, then use checked kind and denotation lemmas.
  Opacity is a proof-engineering aid, not an assumed equation or disabled
  kernel check.
- `change` with an unspecified right-hand side could not infer its Z term;
  write the exact existing product/modulo expression.
- Free-list membership produces the equality in the opposite orientation to
  the operand/fresh-block inequality; inspect and use symmetry.

The archived proof files contain only completed proofs. Temporary probes were
inspected interactively, not compiled as unfinished proofs. Keep speculative
tactics bounded, inspect the actual leaf after failure, and reuse compiled
prefixes instead of repeatedly rebuilding unchanged arithmetic.

## Coordination and acceptance boundaries

Claude owns shared environment-builder, memcpy/SHA and Elements work in the
sibling worktree; these reservations do not overlap scalar multiplication.
The nullable tappath correction is independently preserved in
`../bitcoin-tappath-nullable`, but registry and builder-chain integration remain
separate tasks. Do not conflate reported builder results with their acceptance
in this checkout or with linkage to this generated program.

Preserve unrelated dirty registry/range/SHA/field-negate work. Main accepted
coverage last checked at 351/533; the isolated scalar-add 359/533 candidate is
still pending main integration. This archive adds zero. Do not accept unrelated
dirty snapshots as a side effect. Keep frequent signed atomic local commits,
never push, and leave the all-jet goal active until all public roots are checked.
