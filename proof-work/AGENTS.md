# Preserved Coq proof work

For formal verification tasks in this directory, read and follow
`../Coq/AGENTS.md`, including its task scope and mismatch-reporting workflow.
This applies to archived `.v.source` files and experiments copied into an
external tree as part of the task. Follow `README.md` for handling archived
candidates.

When proving or checking an existing implementation against an existing
specification, leave the implementation, generated ASTs and canonical
specifications unchanged. Record mismatches with evidence and their effect
on proof scope in `Coq/C/JET_*_MISMATCHES.md` (relative to the repository
root), then continue unaffected proof work.

These verification-only restrictions do not prohibit a later task explicitly
requesting implementation or specification development, improvement or a
mismatch fix. Encountering a mismatch during verification does not itself
authorize such a fix.
