# Original-C field predicate candidate

This patch preserves the 18 original-C `fe_is_odd`/`fe_is_zero` proof modules,
two source checker scripts and the candidate build/coverage/snapshot changes.
Its reviewed proof modules, checkers and registration were integrated in
`cafb9b31`, with separate full acceptance passing. The active registry is
349/533. This archive reproduces the historical candidate, not the current
accepted tree; its retained snapshots are not an acceptance receipt.

The manifest pins the original base, candidate head and every changed file.
The original candidate is preserved on `codex/secp-field-predicates` in the
fork. Apply `candidate.patch` to an external checkout of `base_commit` to
reproduce that historical tree. Inherited domain/fidelity review remains open.
