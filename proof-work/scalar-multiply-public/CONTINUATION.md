# Continue after the complete public multiplication proof

Last completed declaration:
`OwnC.jet_secp_scalar_multiply_local.scalar_multiply_literal_local_spec`.
This is a public C-to-literal-Simplicity frame contract, not a body/helper-only
theorem. All normalized reader storage, values, writer representation and
ownership facts are derived internally. The final terminal verification
scope is recorded in `REVIEW.json`.

The previous `../scalar-mul-literal/CONTINUATION.md` ownership/readers/public
wrapper tasks are now discharged by these 14 modules. Do not restart them.
There are no open proof goals in this archive.

## Integrate the checked candidate without accepting unrelated dirty work

1. Use an isolated reconciled candidate. The pending scalar-add tree
   `/tmp/jet-scalar-add-integration.RxsuOy/Coq` already passed its own 359/533
   acceptance; main integration is still separate. Do not alter its frozen
   evidence or the immutable dependency base.
2. Promote the exact checked scalar multiplication dependency chain into `C`
   modules: the earlier `MulC`, `LifeC`, `PubC` archives plus this `OwnC`
   archive. Rewrite only namespace imports, then explicitly rebuild the whole
   changed closure. A `.vo` compiled under a different logical module name is
   not a portable replacement for that rebuild.
3. Reuse the scalar-add candidate's `C.jet_secp_scalar_add_reader_support`,
   `C.jet_secp_scalar_add_two_reads` and `C.jet_secp_scalar_writer_word`.
   The temporary reader copies here differ only by namespace/import and
   removed Print-Assumptions footer; do not register duplicate helper copies.
   Public wrapper modules here are genuinely adapted to multiplication's
   function/void call and must remain distinct.
4. Register the new module/result/definition inventory and select
   `C.jet_secp_scalar_multiply_local.scalar_multiply_literal_local_spec` for
   `simplicity_scalar_multiply` against literal `canonical_scalar_multiply`.
   Include existing `canonical_scalar_multiply_parametric` where the
   registry/evaluator specification audit requires it. This candidate may
   add **one** jet, never 29 helpers. The literal term and public contract
   definitions were printed explicitly in this archive's driver.
5. Generate and review full type/definition/dependency changes. Ensure the
   root still has only the original general frame/input/cursor preconditions,
   no assumed execution/output/free or intermediate representation. Validate
   the canonical target/source identity and generation configuration.
6. Freeze inputs and run the integrated acceptance gate **without update
   flags**. Report terminal status/logs and exact coverage. Main's currently
   dirty unrelated snapshots are not acceptance evidence and must not be
   accepted or committed as a side effect.

The current source identity check is not a newly run full AST regeneration.
Retain that distinction during promotion. If integration uses the scalar-add
candidate, one additional accepted multiplication jet would make 360/533;
that is a prediction, not current accepted coverage.

## Next proof: square's actual shared input pointer

The public square jet calls `scalar_mul(a,a,a)`, not the two-owned-input
contract used by multiply. The current public multiplication theorem covers
equal **values** but cannot be applied to duplicate ownership of one block.

Prove the product helper with fresh layout `[l,a]`, both input arguments
pointing to a and a value/rho adapter duplicating the four input limbs in the
checked numeric product. Reuse the compact executor and column arithmetic,
but formally establish the actual symbolic execution/source and denotation
maps for that layout. Then reuse the product-to-reduction and full function
allocation/free boundaries through exact adapters. Do not assume separation
of a from itself or invent a separate scalar_sqr C helper.

Public square then reuses a single actual scalar reader, the shared-input
helper, the writer and the two-local wrapper lifecycle. Its literal term is
`iden &&& iden >>> canonical_scalar_multiply`. Arithmetic modulo identities
remain internal bridges, not the public specification.

## Engineering lessons retained

- Keeping the real post-product b representation solved the missing cleanup
  permission; the broad outside-both-operands frame alone could not do it.
- Public multiplication uses a void helper return. Reuse addition's wrapper
  structure only after adapting the actual Tfunction result and call value;
  the new body-equality proof checks this against the unchanged generated AST.
- Explicitly import the defining canonical scalar module when using
  `canonical_scalar_normalize`; importing its consumers does not export it.
- Mechanical name adaptation must distinguish `scalar_multiply` (public jet
  and literal term) from `scalar_mul` (the internal C helper). The archived
  source is now correctly named/typed and compiled through the final Qed.
- Keep sources frozen during audits, and poll the exact live session. All
  recorded current checks are terminal; do not infer a still-running build
  from an old scratch log or receipt.

No overlap with Claude's shared environment/Elements reservation. Keep the
all-533-jet goal intact and active until every in-scope public root is checked.
Signed atomic local commits only; never push.
