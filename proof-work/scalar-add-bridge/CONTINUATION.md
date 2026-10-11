# Next: two actual readers and the public scalar-add caller

The owned-input representation and both actual scalar-reader calls are now
compiled and independently audited in `../scalar-add-readers`. Its
`CONTINUATION.md` supersedes steps 1--3 below. Resume at composing the
read/read/add/write chain and original public lifecycle, not re-proving the
reader or owned-input pieces. This older checkpoint remains immutable.

Last verified declaration:
`AddC.jet_secp_scalar_add_literal_owned.eval_scalar_add_literal_owned`.
All eight results in this archive and all 37 helper results in `../scalar-add`
have terminal fresh compile/kernel/type/dependency checks. No current failing
Coq goal remains in these files. Neither archive adds public jet coverage.

1. Build `scalar_add_initial_regs` from two disjoint owned scalar stores.
   Reuse `region_u64`, `region_with_freeable`, `rep_add` and the unary
   `scalar_writer_initial_rep_from_storage` pattern. The locals are 32 bytes,
   unlike field-add's 40-byte locals; do not reuse the field layout blindly.
2. Define the combined eight-limb environment from the two actual reader
   outputs (indices 0..3 and 4..7). Derive both weighted canonical-normalize
   values using `scalar_reader_storage_for_serializer` / its limb-value
   theorem, not assumed reader execution or output in a public theorem.
3. Reuse `field_pair_input_slices` (it is generic Word256-pair encoding)
   to derive input slices at `rc` and `rc+256`. Instantiate
   `eval_scalar_reader_owned` twice, preserving the first scalar while the
   second reader runs. Prove separation/freshness and cursor `rc+512` facts.
4. Apply the checked literal helper bridge; retain both actual Freeable
   regions. Instantiate the real scalar writer for the canonical add result
   (not for a newly normalized substitute). Reuse byte encoding and writer
   ownership/frame lemmas from normalize/negate.
5. Inspect the unchanged `f_simplicity_scalar_add` AST first. Prove actual
   three-local entry (`src`16 + `a`32 + `b`32), by-value source copy,
   read/read/add/write/true-return sequencing and three frees. The arithmetic
   helper returns int but the public call discards it; use the actual type.
6. Public root must be exactly `secp_jet_local_spec f_simplicity_scalar_add
   (Ty.Prod (Word 8) (Word 8)) (Word 8)
   (@canonical_scalar_add Alg.CoreFunSem)` without assumed calls, output or
   free. Only after independent audit, source gates, normal registry review
   and full acceptance may it count as public progress.

Working build command (from the frozen normal candidate's Coq directory):

```sh
export PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH
ulimit -S -s 65520
bash build-jets.sh --coqc -R /tmp/jet-scalar-add.u1U2Ti AddC /tmp/jet-scalar-add.u1U2Ti/jet_secp_scalar_add_literal_owned.v
```

Do not edit the completed checkpoint's sources for new public experiments;
use fresh modules. Inspect actual `Show` after a failed tactic, bound symbolic
reduction to 10 seconds, keep scalars symbolic, and reuse the compiled prefix.

The separate full normal scalar acceptance remains session **83287**; latest
observed log: build passed, `coqchk passed on 829 modules`, assumption gate
running. Preserve candidate inputs and poll this existing session, not a new
audit. Instructions and fingerprint remain in `../scalar-integration`.
Main coverage is still 351/533; candidate 358/533 is provisional isolated.
Claude reserves Elements TU/linkage/getter modules; there is no overlap.
