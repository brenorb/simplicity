# Repository consolidation, 2026-10-06

Scope: consolidate ready work into `brenorb/simplicity:feat/jet-equivalence`.
The inherited fidelity review remains **partial**. No new jet is registered.

## Integrated work

- `d61df9c1`: preserve the initial review of revision `33dc0e5f`, explicitly
  labelled historical; current status remains in `JET_INHERITED_REVIEW.md`.
- `3d1044cc`: preserve the preparatory Elements translation unit and generation
  script. Shell syntax and actual pinned-source generation pass. The generated
  AST is a local verification artifact; no accepted Elements proof is claimed.
- `063e3b04837b0eeffc161c5d4dbaea4a7a7af7ae`: accept the frame-object exclusive-end correction.
  `frame_base_valid` now allows `base+16 <= max_unsigned+1`. Only this semantic
  definition changes. Existing theorem types, conclusions, all other definitions
  and all per-theorem/library assumption sets are unchanged. The divmod128
  change isolates a closed constant inside the proof and changes no declaration.

Independent `check-jets.sh --accept` completes with **exit 0**, without update
or no-build flags. It includes the same preparatory Elements inputs as the
consolidated branch. The integrated fingerprint is identical to the audited
input: `c92e9fba3f64de4713a8fcb317f9982f07f85afd162ee892af7e740d5679280c`.
The check includes a build, 583 kernel modules,
3,534 assumption records, reviewed contract snapshots, negative tests, 240
pinned source inputs, and direct comparison of all four accepted ASTs.

Current verification log: `/tmp/jet-20261006-consolidation-final-accept.log`.
The accompanying JSON records hashes, scope and deferred work. Historical
accepted receipts are preserved in Git history; the old temporary
`/tmp/jet-consolidation-final-accept.log` is unavailable and is not a current
verification log. Interrupted runs are not counted as acceptance.

## Unaccepted candidates consolidated as source archives

- `codex/frame-range-contract`, head `00536113eb285b109f00c28a0fd22de66b05ec35`:
  the broader same-block range correction remains unaccepted. Its exact patch
  series is versioned in `../../proof-work/range/`, and the original candidate
  history is retained as `codex/frame-range-contract` in the fork.
  Prior scoped receipts cover 91 changed modules with kernel checks; another
  12 modules were built and source-reviewed, then saved in five atomic commits.
  Their separate kernel run was stopped and has no passing result. The whole
  consumer build still fails at the old tuple in full_multiply8, and copy and
  symbolic-executor consumers still require the old separation interface.
  A full correction/snapshot review/acceptance is needed before integration.
  Its copy of the endpoint fix does not make the entire range branch accepted.
- The field odd/zero candidate is versioned as an exact patch under
  `../../proof-work/secp-field-predicates/`, with original candidate commits on
  `codex/secp-field-predicates`. Its registration/snapshot changes are not
  applied to the accepted tree. Complete scalar/u128, SHA and review-witness
  sources are also versioned under `../../proof-work/`, with exact hashes.

All useful source work identified in the branches/worktrees and 84-file scratch
inventory is now versioned on the main topic branch. Candidate manifests retain
its incomplete/unaccepted status. Exact patch replay and source hashes pass;
proof completion and acceptance remain separate obligations.

`JET_PROOF_BACKLOG.md` replaces the stale chronological `JET_PROGRESS.md`.
The old prototype worktree is removed after preserving its four untracked files
in local Trash. `../../proof-work/README.md` records recovery and verification.

## Local-only artifacts

`Coq/__pycache__/`, `brag-output/` and `jet-proof-review.patch` remain untracked.
The generated Elements AST and intermediate verification artifacts remain local.
No upstream repository, main/master branch, production C implementation or
canonical specification is modified.

The registered inventory stays **347/533**, including **104 conditional on
memcpy_model**. This is an inventory, not exhaustive fidelity certification.
The broader same-block/address/constructor and per-entry canonical review
obligations remain in `JET_INHERITED_REVIEW.md`.
