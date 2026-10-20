# Shared hash-word semantics and Elements stream getters

## First completed checkpoint

`C.jet_sha_hash_words_reader` freshly compiled and its15 results / one
definition were reported completely by:

The helper generalizes only the environment-dependent evaluation layer of
the existing literal `hashLoop` / `hash_words_spec` programs. It reuses the
already checked generic `for_while_program_reader_sem`, traversal theorems,
`loop_step`, `loop_prefix_some`, finite-counter bounds, SHA context absorption
and finalization. It handles empty arrays and both early-stop/counter-full
paths for arbitrary widths and environments, without a new primitive
signature, artificial Bitcoin environment witness or assumed hash oracle.

The exported interface is `hash_words_reader_sem`.

## Seven complete C endpoints now compiled and reported

`C.jet_elements_words_hash_program` instantiates that interface with the actual
Elements primitive algebra. It proves the whole original C getters against
the same literal hash-word programs for output scripts/range proofs/surjection
proofs, input scripts/sequences/scriptSigs and tappath. Each endpoint composes
the existing complete `elements_hash_getter_writeHash_local` execution proof,
including original function/body, linked global environment, field layout,
separated frame/output/prefix/load guarantees and all cursor positions covered
by that contract. No desired execution or output fact is added as a premise.

The cached-memory representation remains explicit: it requires each field to
contain the hash determined by the represented raw scripts, proof bytes,
sequences or path. This does **not** prove the actual C environment builders
populate those fields. Confidential proofs retain the existing raw-byte
primitive interpretation; no arbitrary independent digest input replaces it.

The separate selected canonical source review also completed, with203
read-only corruptions rejected; its exact scope and receipt are in
`../elements-stream-source/`. It establishes selected source correspondence,
not formal host-runtime equivalence or C cache-builder correctness.
