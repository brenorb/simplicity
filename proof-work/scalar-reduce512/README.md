# Checked original scalar_reduce_512 execution

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

From the dependency Coq directory, pinned Coq 8.17.1 on PATH, stack 65520 KiB:
