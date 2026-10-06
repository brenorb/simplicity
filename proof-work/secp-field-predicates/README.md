# Original-C field predicate candidate

This patch preserves the 18 original-C `fe_is_odd`/`fe_is_zero` proof modules,
two source checker scripts and the candidate build/coverage/snapshot changes.
It is not applied to the active Coq tree. Candidate snapshots and registration
changes do not constitute acceptance. The active registry remains 347/533.

The manifest pins the original base, candidate head and every changed file.
The original candidate is preserved on `codex/secp-field-predicates` in the
fork. Apply `candidate.patch` to an external checkout of `base_commit` to
reproduce it. Full acceptance and inherited-review priorities remain open.
