# Read-only cumulative main reconciliation checkpoint

This is a historical comparison, not application or acceptance. The full plan
is `/tmp/jet-square-main-plan.pG9VYx/PLAN.json`, SHA-256
`cab4eed4e46b2b90a128ab18eacfc0cd46be3811f8f967a0b6c827789d749d05`.
`MAIN-PLAN-SUMMARY.json` retains the summary and separately captures current
worktree/index metadata hashes. Always recompute before later application.

## Current preservation evidence

- 872 existing `.v` sources are identical; no Coq source conflicts.
- 285 cumulative source additions and 26 new gate/provenance assets are
  proposed. The existing main-only `C/jet_secp_fe_negate_math.v` stays untouched.
- All five inventories are byte-prefix extensions, preserving every old row
  in order: 285 project entries, 1,081 results, 607 definitions and ten jets.
- All 3,733 main dependency records and 5,611 ordered contract records are
  unchanged. Candidate adds 1,688 contract records. Kernel allowlist is identical.
- Forty-four existing gate/provenance assets match. The only asset differences
  are the four explicitly reviewed gate scripts below; no hidden asset overwrite
  is proposed.
- Twelve metadata files have separate worktree/index hashes. The entire
  preexisting staged patch SHA-256 remained
  `f2083389e06d3a5aed12c83d0aae554895eab94eef8e107c5d445f9268d86bbe`
  through planning/testing. No index, main proof, registry or candidate input
  was changed. Saving the separate diagnostic report is not an input edit.

## Gate differences reviewed

`check-jets.sh` retains every existing line and adds source/negative checks for
point/infinity/ge-negate/scalar/normalize/negate/add/multiply/square milestones.
It requires the 26 missing supporting Python files; adding hook lines without
those files would not integrate the proof correctly.

`jet-coverage.py` retains all old accepted function names and adds only the ten
selected, reviewed original secp C functions to its full-contract whitelist.
The statement and exact C-function checks are not relaxed. New source gates
check literal specialization separately.

`test-jet-coverage.py` adds a ten-jet mutation loop. All old test code, including
the existing field-addition rejection cases in the unstaged worktree, remains
unchanged. Wrong function, wrong global/whole contract and added false premises
are rejected for every newly selected entry.

`audit-jet-contracts.sh` adds only a no-open `Require` for the existing
`C.jet_secp_umul128_exec` import. All qualified Check/Print commands remain.
This is the previously checked fix for seven short-name collisions, preserving
inherited Print bytes rather than rewriting their expectations.

These reviewed diffs are tied to the exact source hashes in the plan. They do
not authorize replacing a later-modified gate. Existing staged/unstaged changes
and documentation/range/SHA work remain separate and must not be accidentally
included by a broad commit or overwrite.

## Reproduce checks

```sh
python3 -B proof-work/scalar-square-integration/plan-main.py --candidate-coq /tmp/jet-scalar-square-integration.MAhL2g/Coq --summary
python3 -B proof-work/scalar-square-integration/test-plan.py /tmp/jet-square-main-plan.pG9VYx/PLAN.json
```

For the full report, omit `--summary`. An optional `--report` may save a fresh
JSON through `apply_patch` in a dedicated `jet-square-main-plan.*` temporary
directory, never in Coq/audit inputs. Fifteen in-memory unsafe proposals are
rejected (source/dependency/contract drift, discarded inventory, path escape,
unreviewed conflict and false installation claims).

## Actual next action and live audit

Full square acceptance **41316** remains live; the 937-module kernel passed and
the last observed phase was the assumption gate. Keep its sources/metadata/
C/Haskell frozen and poll that same actual session. A quiet log or observation
timeout is not terminal; never restart a duplicate run.

After terminal success, verify all remaining gates/four AST comparisons and the
frozen fingerprint, revalidate normal review/mutations, and record its receipt.
Then recompute this plan, resolve all exact hashes and apply scoped additions
without changing the index or consuming unrelated work. Full main acceptance
is still separate. Candidate 361/533 is provisional until its gate completes;
main remains 351/533. The all-533 goal stays active. Local signed commits only;
never push. Claude's shared/Elements reservation is untouched.
