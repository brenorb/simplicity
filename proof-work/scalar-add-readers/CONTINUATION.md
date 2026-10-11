# Continue from checked scalar readers, not from scratch

Last verified declaration:
`AddC.jet_secp_scalar_add_two_reads.eval_scalar_add_two_readers`.
All 15 results in this archive, eight in `../scalar-add-bridge`, and 37 in
`../scalar-add` have terminal compile/kernel/type/dependency checks. There
is no failing Coq goal in these sources. No public coverage is added.

## Completed pieces

- `eval_scalar_add_two_readers` derives two original `f_read_scalar` calls,
  both canonical normalized stores, source cursor `rc+512`, Freeable
  ownership for both scalars/source local, invariant and both memory frames.
- `eval_scalar_add_from_normalized_scalars` derives the actual arithmetic
  helper and literal add-result writer representation from those stores.
- `scalar_at_lframe` and `scalar_preserved_across_other_read` derive
  preservation from actual reader framing; do not assume preservation.
- Scalar input/region construction uses the real 32-byte sizes, not field
  sizes. `scalar_add_reader_rho` covers indices 0..3 and 4..7 explicitly.

## Next obligations

1. Compose both checked contracts in a fresh read/read/add/write module.
   Derive input slices with the generic `field_pair_input_slices`. Preserve
   the third, 16-byte source-frame local across the arithmetic helper:
   its actual footprint only mentions the two scalar blocks. Its exact
   loads/cursor and Freeable permissions must refer to the latest memory.
2. Build the actual writer invariant for the literal add result and apply
   the existing scalar writer. Prefer a generic writer-for-Word256 adapter
   (`scalar_writer_outs_numeric` + `be_bytes_canonical_encoding`) to proving
   the target is a fixed point of normalization solely to fit the older
   normalize-specific writer theorem. The public specification must remain
   `canonical_scalar_add`, not a substituted numerical/normalized function.
   Preserve the second scalar and source-frame local across the writer.
3. Inspect unchanged `f_simplicity_scalar_add` AST. Prove public entry and
   source copy for three locals (`src`16 + `a`32 + `b`32), the original
   read/read/add/write/return sequencing, and all three actual frees. The
   helper returns `int` but the public call discards it; the public result is
   true. Reuse field-add lifecycle structure with explicit size/AST adapters.
4. Public root must be exactly `secp_jet_local_spec f_simplicity_scalar_add
   (Ty.Prod (Word 8) (Word 8)) (Word 8)
   (@canonical_scalar_add Alg.CoreFunSem)` with no assumed helper/reader/
   writer executions, output or successful frees. Then audit literal
   correspondence and dependencies/contracts, normal registry transport,
   negative gates and full acceptance before counting public progress.

Working compile command, from `/tmp/jet-scalar-integration.XAMDsw/Coq`:

```sh
export PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH
ulimit -S -s 65520
bash build-jets.sh --coqc -R /tmp/jet-scalar-add.u1U2Ti AddC /tmp/jet-scalar-add.u1U2Ti/jet_secp_scalar_add_two_reads.v
```

Do not mutate checkpoint inputs for new experiments; use fresh modules.
Recent diagnosed pitfalls: `region_with_freeable` needs an explicit
`free_region` conversion when the goal is a bare record; the initial reader
representation lemma lives in `C.jet_secp_scalar_public_entry`; imported
Core notation `H` collides with a hypothesis called `H` in `proj2 H` (use
`HInv`). Inspect actual `Show`, then change only the diagnosed mismatch.

## Separate running acceptance

Session **83287** still owns normal normalize/negate full acceptance in
`/tmp/jet-scalar-integration.XAMDsw/Coq`. Latest observed log: build passed,
`coqchk passed on 829 modules`, assumption gate running. Preserve all inputs
and poll this existing run. Fingerprint/instructions remain in
`../scalar-integration/CONTINUATION.md`. Candidate 358/533 is provisional
isolated, not main registration; main is 351/533.

All-533 goal remains active and unfinished. Claude reserves Elements
TU/linkage/getter foundations and shared obligations; no overlap. Preserve
main mixed staged/unstaged changes. Signed local atomic commits; no pushes.
