# Side-branch integration ledger, 2026-10-19

This records every side branch and worktree that was compared with
`feat/jet-equivalence` at `d7515911`, and what happened to its work. The
comparison was by file content, not by commit. The branch history was rewritten
around 2026-10-16 (backup: `codex/backup-jet-equivalence-20261016`), so older
branches share no recent merge base with it, and a `git merge` would replay
hundreds of already-integrated commits.

Method: for each source, list the files it changed relative to its merge base
with `feat/jet-equivalence`. Each file is then classified as **identical** to
HEAD, **superseded** (its version appears earlier in HEAD's history, so HEAD has
moved past it), **divergent** (never in HEAD) or **missing**.

| Source | Tip | Result |
| --- | --- | --- |
| `codex/backup-jet-equivalence-20261016` | `4b7157a2` | 4277 identical; the rest superseded except `Coq/Simplicity/Primitive/Bitcoin.v` (see below). Nothing to integrate. |
| Codex worktree `b53f` (detached) | `8bdca3fd` | 2000 identical; 11 superseded / `Bitcoin.v`. Nothing to integrate. |
| Codex worktree `d645` (detached) | `3d1f2e6d` | 1593 identical; 7 superseded / `Bitcoin.v`. Nothing to integrate. |
| Codex worktree `rocq-mcp-trial` (detached) | `71a2f88a` | 2003 identical; 13 superseded / `Bitcoin.v`. Nothing to integrate. |
| Codex worktree `11f7` (detached) | `c3588750` | Ancestor of HEAD. Nothing to integrate. |
| `fork/codex/secp-field-predicates` | `9e79736e` | Integrated earlier (`cafb9b31`, see `proof-work/README.md`); remaining differences superseded. |
| `fork/codex/frame-range-contract` | `00536113` | Integrated earlier (range integration, `proof-work/range`); remaining differences superseded. |
| `claude/shared-obligations` | `30404fac` | Its tip is the frozen snapshot already reviewed and imported by `proof-work/shared-foundations-integration`, `claude-remainder-integration`, `linked-repair`, `sha-startup-integration` and `secp-checked-conversions`. Every `.v` source is in HEAD, some under the repaired forms those packets record. The files not imported (the broad build/audit scripts, old registry generators, `COORDINATION.md`, `SHARED_*`) were excluded on purpose, as documented in `claude-remainder-integration/STATUS.md` §"What was intentionally not integrated". |
| `codex/fe-multiply-parallel` | `ef4aa19c` | **Duplicate proofs** of `fe_multiply` and `fe_square`. Archived in [`fe-multiply-parallel/`](fe-multiply-parallel/ARCHIVE.md); the main proofs remain the registered ones. |
| `codex/fe-multiply-integration` | `a8bfb8b1` | Docs, the `mul-review` gate and the registration commit are archived with the above. Not applied: the registration (`dd4579a7`, it would register the duplicates); the field-negation chain in `Coq/C` (same bytes as the main agent's uncommitted candidate, already archived in `secp-field-literal/inherited`); and the u128 project listing (`41a1dc70`, already in the main checkout's uncommitted `_CoqProject`). |
| `fork/feat/jet-equivalence` | `66de0fed` | Ancestor of HEAD (two commits behind). |

## Divergence not taken: `Coq/Simplicity/Primitive/Bitcoin.v`

The pre-rewrite branches carry an altered Bitcoin model, with `moneyRange`
fields removed, `0 <= Zlength sigTxOut`, and the fee sign flipped. HEAD restored
the frozen upstream file on purpose (`35d1e347`), and it now matches
`origin/master` and the `91d89bac` target guard. Preserving canonical specifications is a
project rule (`Coq/AGENTS.md`), so the altered model was not reintroduced. The
open consequences are described in
`fe-multiply-parallel/BITCOIN-BLOCKER-PROPOSAL.md`.

## Duplicate proofs

| Jet | Kept (registered path) | Archived alternative | Reason |
| --- | --- | --- | --- |
| `simplicity_fe_multiply` | `proof-work/secp-field-literal` (`fe_multiply_literal_local_spec`) | `fe-multiply-parallel/modules/jet_parallel_fe_mul_*` | Same statement. You decided 2026-10-19 to keep the main proof (`fe-multiply-parallel/HANDOFF.md`); it has more source-review coverage, and later main work builds on it. |
| `simplicity_fe_square` | `proof-work/secp-square-*` (`C.jet_secp_square_local.fe_square_local_spec`) | `fe-multiply-parallel/modules/jet_parallel_fe_sqr_*` | Same as above. |
| `simplicity_fe_negate` | — | — | Not a duplicate. One candidate, byte-identical in all four places it appears. |

## Left untouched

- The main checkout's uncommitted work (staged SHA support, field-negation
  modules, registry edits). Per your instruction, nothing was read into or
  written over it.
- Uncommitted files in the Codex worktrees: see the section below.
- The side branches themselves. They were not deleted.

## Uncommitted files in the Codex worktrees

These are not branches, but they were checked so that no proof would be missed.
Each uncommitted file was compared by content with HEAD and with the main
checkout's working tree:

| Worktree | Matches main checkout | Differs from both | What the differing files are |
| --- | ---: | ---: | --- |
| `11f7` | 3611 | 0 | none |
| `b53f` | 3583 | 11 | registry/snapshot/project files (`jet_*.expected`, `jet_coverage.tsv`, `jet_public_theorems.txt`, `jet_contract_definitions.txt`, `_CoqProject*`, `audit-jet-contracts.sh`, …) from an older stage of the main agent's in-progress registration |
| `d645` | 3583 | 11 | the same kind of files as `b53f` |
| `rocq-mcp-trial` | 0 | 21 | `proof-work/rocq-mcp-trial/`: a 2026-10-15 evaluation of the rocq-mcp interactive proof interface (benchmarks, logs, launch scripts). No jet proofs; `proof-work/rocq-mcp` already holds the committed launcher. |

None of these files is a new jet proof, so none were imported. The registry files are
regenerated during acceptance, and taking an older copy would conflict with the
main agent's live edits.

## Completed local continuation

The main checkout's index and working source states were preserved by signed
commits `d46f2c16` and `abc06c23` on `wip/codex-20261019`, then merged before
rewriting the integration history. Both original working folders have also been
checked byte-for-byte against that saved source state. No unique proof is lost.

The selected primary endpoints are now ordinary modules
`C.jet_secp_multiply_literal_jet.fe_multiply_literal_local_spec` and
`C.jet_secp_square_local.fe_square_local_spec`. The alternative remains in
`fe-multiply-parallel`; its ARCHIVE.md records equivalent logical scope, the
source-review/downstream reasons for the choice, and its faster execution model.
The current pending-jet reconciliation is in `Coq/C/JET_ACCEPTANCE.md`.

Original side branches and worktrees remain available. Removing them requires
separate user approval; the old hash references above identify the backup
history and are intentionally preserved as provenance.
