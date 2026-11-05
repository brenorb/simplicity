# Preparing one bound witness for vector evaluation

`Types.boundProgram kernel` describes exactly `witness value >>> kernel`.
The `unProg` selector returns that complete source expression. The normal
measurement, candidate overlay, serializers, DAG mining and ablations consume
that expression, including the witness and its actual inferred type. No jet,
consensus encoding, cost or transaction primitive changes.

`Run.runVectors` can compile an eligible kernel once for one vector batch. It
does not retain a compiled graph in the corpus registry. A source interpreter
checks both branches and refuses kernels containing any internal `witness` or
`disconnect`; such programs use ordinary whole-program evaluation. A public
`Jet` specification cannot contain either extension by its rank-polymorphic
`Assert`/`Primitive` interface.

For every prepared vector, the runner checks all of the following:

1. The input type equals the prepared input type, using `equalTyReflect` and its
   equality proof rather than an unsafe cast.
2. The raw kernel's annotated Merkle root matches. This binds its types,
   constants, primitives, assertion roots and any literal jet specification.
   There are no internal witness values or delegated expressions to substitute.
3. The composition CMR, computed with the public commitment-root algebra for
   `witness value >>> jettedKernel`, equals the independently computed CMR of
   the complete canonical first program.

Any mismatch takes the ordinary whole-program path, which still checks the
vector's complete jet-substituted CMR against the baseline. In particular,
standalone kernel type inference may erase unused fields differently; a jet-root
difference cannot silently pass the composition check. Changed kernels/types
are not treated as belonging to the first program merely because they appear
in the same entry.

Evaluation uses the compiled **jet-substituted** kernel and the actual bound
value. The transaction environment receives the complete program's CMR, so
`ScriptCMR` and transaction signatures retain their ordinary environment.
This is a functional-evaluation optimization; the full expression remains the
source of every static cost and serialized-witness measurement.

Regression tests compare prepared and whole-program substitution for projections
with unused1024-bit input, both case branches, whole-program `ScriptCMR`, changed
constants, changed input widths, internal witnesses and delegation. They also
compare canonical program/witness bitstrings and normal cost. All three test
cases passed in the initial targeted run and again at the start of the current
39-test cohort; its preserved completion is required before final reporting.

Partially apply `boundProgram` outside the vector encoder to share the source
fingerprint. `tools/run_recorded.py` preserves each validation cohort's output,
launch source hashes and a frozen copy of its exact executable. Those source
hashes describe the checkout, not a claim of compiler attestation. A later
rebuild cannot replace that cohort's executable identity.
