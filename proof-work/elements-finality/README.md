# Elements TxIsFinal: checked canonical C contract, not yet registered

The existing `C.jet_elements_is_final_local.elements_tx_is_final_local_spec`
executes the actual `simplicity_tx_is_final` in `elements_ge` and returns the
semantics of the canonical `TimeLock.txIsFinal` Simplicity program, with its
InputSequence primitive. The implementation reads the cached `isFinal` byte
and writes one bit. The proof relates that byte to the result of the program's
bounded counter loop. It does not replace the public specification with a
mathematical predicate or assume the C execution.

## Evidence

Seven modules were explicitly freshly compiled in dependency order, including
the finality specification, C field helper and actual-C endpoint. All 43
helper/final result types and 22 definitions were printed without elision or
unresolved placeholders; per-result assumptions were checked. The public C
endpoint retains exactly the six inherited assumptions, with no additional
library model. Recursive `coqchk -silent -o` on both finality roots passed;
unsafe fixpoints and assumed positivity remain absent. Exact regeneration of
`jets_elements.v` from the production Elements unit also passed.

The source guard checks canonical dispatch, the complete `txIsFinal` program,
both `forWhile` recursion clauses, `all`/conjunction, routing/bit/sum helpers,
the corresponding Coq ports, the exact representation and the entire C
contract. It reuses the previously reviewed InputSequence and literal word
representation guard. Thirty-one source mutations are rejected, including
branch reversal, counter-width changes, swapped nested-counter routing,
wrong primitives, weakened framing, altered field offsets and vacuous
premises. Invalid proof text is never compiled.

The `forallb sequence_final` equation is an intermediate semantic bridge and
the initial physical/logical representation of the cache; it is not the final
specification. The final theorem targets the primitive Simplicity program.
The separated frame/memory guarantees and initial environment relation are
preserved: the transaction pointer is loaded from the environment at offset 0,
the unsigned byte from transaction offset 752, and its footprint is retained.
This batch does not prove that an actual environment builder establishes that
cache relation, does not prove evaluator integration, and does not broaden the
LP64/RECKLESS configuration covered by the existing C model.

## Continuation

Both commands should pass before any admission candidate is assembled.
Normal manifests, public-result/definition registries, snapshots and coverage
have not been changed by this batch. Coverage added is **zero**; the normal
registration/full-acceptance procedure remains required. Main remains frozen
while the sequence actual-main audit and direct-getter isolated audit run.

The natural next family is `tx_lock_height` / `tx_lock_time`: their existing
actual-C proofs compose this same finality loop with LockTime and parseLock.
Review their canonical composition and representation, freshly check the
additional dependencies, and reuse these loop/primitive source checks rather
than copying another finality proof. Do not register any remaining Elements
primitive merely because this one selected clause has been checked.
