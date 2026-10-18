# Original-program entropy helper port

This is a proof-support port of the existing environment-unit execution proof
for `simplicity_generateIssuanceEntropy` to the original Elements jet program.
It is not a new complete `calculate_issuance_entropy` jet equivalence theorem.
The private tree is `/private/tmp/jet-elements-entropy-calls.K31Tpk`.

The eight existing modules keep their theorem statements and proof bodies.
Only imports and the shared local-array lemma name are changed. The ninth
module extracts the exact pure `hash_buffer_regs` formula; it does not import
the environment-only `hashBuffer` function or its execution theorem. `port.py`
checks these byte-exact transformations and rejects five in-memory mutations.

The original Elements AST is unchanged. In the private proof tree only,
`C.jets_sha` is a byte-identical proof-loading copy of `C.jets_elements`.
Closed program/genv equality proofs are explicit verification roots. An
environment-unit execution result is not silently asserted for the jet unit.
Libc, compression dispatch and maximum-counter premises remain explicit.

`verify.py compile PRIVATE_TREE` forces all local dependencies from source,
checks complete type/definition/assumption reports, and records an exact
forced/loaded source-object closure. Compilation or a launch is not kernel
checking. The new per-result profile needs review before a separate recursive
check. No accepted coverage is added.

Remaining: connect the C byte-stream/padding result `entropy_regs` to the
literal canonical calculation program, then derive the actual frame jet's
outpoint/contract reader prefix, helper call, returned struct copy, writer,
return/free and memory framing from initial frames. The completed three
other calculation jets provide the composition pattern, not these premises.
