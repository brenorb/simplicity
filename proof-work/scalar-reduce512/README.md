# Checked original scalar_reduce_512 execution

Three modules / **13 results, five definitions** freshly compile in `MulC`,
scratch `/tmp/jet-scalar-mul.lkomWj`, against the accepted immutable normal
candidate `/tmp/jet-scalar-integration.XAMDsw/Coq`. Last verified declaration:
`MulC.jet_secp_scalar_reduce512_run.eval_scalar_reduce512_owned_loads`.

It takes only `rep rho beta scalar_reduce512_initial_regs m` and proves the
actual unchanged `jets_secp.f_secp256k1_scalar_reduce_512` call, `Vundef`
return, allocation/free of its 15 uint128 locals and real internal helper
calls, all four **current-memory** output expression loads, preservation of
the eight-limb input, final owned representation and outside framing.
The input and previous output values are arbitrary machine words. Regions
are distinct owned 32-/64-byte allocations. This is LP64 / RECKLESS helper
execution, not arbitrary evaluator-frame or assertion-enabled coverage.

**Still open:** the four output limbs have the input's value modulo the
scalar order; original public multiply/square caller lifecycles; their
literal canonical Simplicity program bridges. The output expressions are
derived from the checked execution, not assumed correct. No public
specification is replaced and no coverage entry is added.

## Reuse and avoid diagnosed failures

`jet_secp_compact_shift64` composes the already-proved compact statement
executor with `C.secp_shift64_table_correct`. The shift64 oracle is proved
over the original C helper, including actual loads/stores and call semantics;
it is not an assumed helper execution. Every shift in this run has count 64.
The table's correctness discharges its internal/oracle-call obligations.

The run has **six** zero-result shift64 events, each `mkev 0 12 0 []`.
An attempted empty-log lemma failed with those exact six events; the checked
`scalar_reduce512_log_shift64` retains them. `compact_fun_shift64_sound`
discharges the event predicate using the proved table, not an added event or
correct-output premise at the owned call boundary.

Direct `reflexivity` for the output-region equality timed out at ten seconds
by repeatedly unfolding the large symbolic expressions. Do not extend that
timeout or normalize all four `den` expressions at once. `jet_sx_u64_rebuild`
proves reusable reconstruction from small offset/chunk/initialization checks.
`scalar_reduce512_owned_metadata` computes only those checks, region count,
ownership/writability, and the unchanged input. It then reconstructs the
region equality generically, without reducing the symbolic values.

## Verification

- Fresh fail-fast three-module build **84956**, exit 0.
- Independent kernel closure **95049**, exit 0. Inherited 15-axiom context
  matches; type-in-type, unsafe fixpoints and assumed positivity are empty.
- Fail-fast full-depth type/definition/dependency drivers **70464**, exit 0;
  13 types / five definitions are untruncated and stderr is empty.
- Ten results are closed. The compact soundness theorem and two execution
  roots have exactly the same six inherited execution dependencies.
- `manifest.json` / `REVIEW.json` pin source, driver, output and kernel hashes.
  Read-only review revalidates the checked compact/product prerequisites and
  their source fingerprint. Nine in-memory negative mutations are rejected.

```sh
python3 -B proof-work/scalar-reduce512/review.py
python3 -B proof-work/scalar-reduce512/test-review.py
```

From the dependency Coq directory, pinned Coq 8.17.1 on PATH, stack 65520 KiB:

```sh
bash build-jets.sh --coqc -R /tmp/jet-scalar-mul.lkomWj MulC \
  /tmp/jet-scalar-mul.lkomWj/jet_secp_scalar_reduce512_run.v
bash build-jets.sh --coqchk -silent -o -R /tmp/jet-scalar-mul.lkomWj MulC \
  MulC.jet_secp_scalar_reduce512_run
```

All processes above are terminal. No failing Coq goal remains in these three
files. Do not edit their frozen sources while using this evidence; add new
arithmetic/stage modules. Read `CONTINUATION.md` for the next actual obligation.
Main coverage remains 351/533; accepted isolated scalar-add is 359/533, with
exact main reconciliation/verification pending. Leave Claude's Elements,
memcpy/linkage, SHA startup and constructibility work alone. Local signed
atomic commits only; no pushes or production C/Haskell changes.
