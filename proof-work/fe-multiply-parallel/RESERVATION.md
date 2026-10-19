# Field multiplication — parallel reservation

- Branch: `codex/fe-multiply-parallel` (worktree `simplicity-fe-mul`, sibling of
  the main checkout).
- Starting commit: `de1623ea04745e0053a80eb32e07ea7b2a225749`
  (`feat/jet-equivalence`, "test(coq): kernel-check original calculation helper
  word contracts", signed).
- Reserved (2026-10-18): `simplicity_fe_multiply`, then `simplicity_fe_square`.
- Coordination check before starting: `simplicity-shared/COORDINATION.md`,
  `proof-work/README.md`, `Coq/C/JET_PROOF_BACKLOG.md` and the Codex
  worktrees under `~/.codex/worktrees/*/simplicity` contain no reservation or
  module for field multiplication or squaring; the jets only appear in lists
  of unproved entries. The field-add (`proof-work/fe-add`, integrated) and
  field-negate (main checkout, uncommitted) chains are reused, not modified.

Scope: new modules `Coq/C/jet_parallel_fe_mul_*.v` and evidence in this
directory only. Shared registries, project inventories, snapshots,
allowlists, acceptance tooling and existing helpers are left unchanged;
integration belongs to the main agent.
