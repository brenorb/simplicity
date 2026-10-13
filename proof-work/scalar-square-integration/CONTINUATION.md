# Main audit running; continue borrowed-global lambda work

## Current main checkpoint supersedes historical launch notes below

Actual secp initialization existence has since been proved and kernel-checked
in `../scalar-lambda-startup`: two modules / six results / four definitions;
five results closed. It constructs an actual initialized lambda-memory witness,
not just a conditional initialization lemma. Fresh intended caller frames and
normal registration remain the next steps. Keep historical receipts unchanged.

Lambda advanced beyond the older helper notes: `../scalar-lambda-caller`
now records the full original scalar_multiply_lambda call, literal output,
entry/copy/helpers/return/free, tight readonly-global framing and initialized
state preservation. Eleven modules / 53 results / seven definitions all compile
and pass independent closure kernel checking; 23 negative fixtures passed.
Signed local commits: `03c52c60` shared framing and `4f706818` full caller.
The explicit initialized-global memory boundary remains; no normal registration
or coverage increment. Root has eight inherited Coq/CompCert dependencies,
including standard external/inline-assembly properties, not six. Do not hide
them or replace the literal specification. See that archive's next actions.

Main audit 22185 is still confirmed live. It has now passed all 937 kernel
modules and is at the assumption gate. Its frozen source hash and the entire
preexisting staged-patch hash remain unchanged. Keep polling that same handle;
do not restart or mutate audited main inputs.

The preservation-safe application completed (70639, exit 0): 285 new proof
sources, 26 gate assets and 11 reviewed metadata/gate updates. All 873 existing
sources stayed byte-identical, including main-only work; the entire preexisting
staged patch remained `f2083389e06d3a5aed12c83d0aae554895eab94eef8e107c5d445f9268d86bbe`.
New sources/gates are signed local commit `e73665a1`; existing metadata changes
remain unstaged relative to the preserved user index. No blanket commit occurred.

**Actual-main full acceptance is running as 22185**, not yet accepted. Poll
that handle; do not restart or edit main Coq/C/Haskell audit inputs. Log:
`/tmp/jet-square-main-audit.BLWJ4e/full-acceptance.log`; frozen fingerprint
`2fd541106f2092a42ca83c65b2bdae777eb6e21ffb40a67ec331e2bb341c6ba0`.
`MAIN-INTEGRATION.json` records the launch, not success. Main registry is now
361/533 (257 without an extra library premise, 104 conditional on memcpy_model).
Wait for terminal exit and all gates before claiming main acceptance.

Borrowed-rhs full internal scalar_mul call is separately kernel-checked and
signed as `1538369b`, in `../scalar-mul-borrowed-function`: 3 modules / 7 results /
2 definitions, actual entry/allocation/free and post-free output loads. Public
lambda equivalence remains open. Its global initialization experiment stays
outside audited main in `/tmp/jet-scalar-lambda-global.qHkGK8` (LambdaC).
See the borrowed-function guide; do not assume global initialization, helper
execution, output or free as new public premises.

## Terminal success supersedes historical launch notes

Full acceptance **41316** terminated with exit 0 (terminal chunk **9e91d0**).
All gates and four AST comparisons passed: 937 kernel modules, 4,814 audited
results (2,663 closed). The input fingerprint is unchanged. Post-run review
and negative tests **60887** also terminated with exit 0. `ACCEPTANCE.json`
pins terminal evidence. Do not poll or restart these completed handles.

Isolated **361/533** is now accepted (257 entries without an extra library
premise, 104 explicitly memcpy_model-conditional). Main remains separate; the
next action is the reviewed, preservation-safe main reconciliation below.
Keep the accepted candidate immutable. `AUDIT-RUN.json` is historical launch
evidence, not the final receipt.

Full acceptance is **already running** as actual session **41316**, verified
live by polling that same handle. Log:
`/tmp/jet-scalar-square-integration.MAhL2g/full-acceptance.log`.
`AUDIT-RUN.json` records the actual launch, not success. First poll **41316**;
do not launch another acceptance command or edit any candidate inputs.

Last verified normal declaration:
`C.jet_secp_scalar_square_local.scalar_square_literal_local_spec`.
All 15 changed modules / 47 results compile and pass independent closure
kernel checking. Exact source/type/definition/dependency reviews are terminal
success; `PREPARATION.json` records them. No Coq proof goal is failing.

## Full acceptance

Run `JOBS=1 bash check-jets.sh --accept` in
`/tmp/jet-scalar-square-integration.MAhL2g/Coq` with pinned Coq 8.17.1,
`ulimit -S -s 65520` and a measured 10,800-second process deadline. Use no
update/no-build flags. If already launched, **poll its actual recorded live
handle**, never start a duplicate from an old log or observation timeout.
Do not edit any audit input while it runs. A launch receipt is not success.

Frozen fingerprint:
`7522998e48f1441831821609af464ac2942a5424179077af9ea81ee0a1501176`.
Only terminal exit 0 plus all build/kernel/type/definition/assumption/negative
gates and four AST comparisons establishes acceptance. Revalidate the fingerprint
and read-only normal/public mutation tests afterward. Record actual observed
module/result/coverage counts and terminal log hash in a new `ACCEPTANCE.json`.

The candidate predicts 361/533, but that remains provisional until the full
gate passes. Its accepted parent is multiply 360/533; main is still separate.
All preparation handles are **completed**, not live: **79279** build, **32019**
assumptions, **28600** deep contracts, **51561** snapshot generation, **68228**
closure kernel, **82901** normal review, **36882** normal mutations, **52418**
public mutations (exit 0). Do not poll or restart those checks.

## Main integration after acceptance

Recompute exact source/inventory/snapshot/gate overlap against main's actual
index and worktree using the multiply read-only planner and ordered parser.
The accepted parent and square proof archives remain immutable. Preserve
staged/unstaged range/SHA/registry/field-negate work and main-only files. The
previous main plan had no source conflicts, but its counts are historical;
square adds 15 more sources, not permission for wholesale checkout replacement.
Review overlaps before applying and fully verify the resulting main tree.

`plan-main.py`, `MAIN-PLAN-SUMMARY.json` and `MAIN-RECONCILIATION.md` now record
an exact read-only checkpoint: 285 new sources, 26 new gate assets, no source
conflicts, old rows/contracts/dependencies unchanged, and all four gate diffs
reviewed as preserving existing code. Separate index/worktree hashes and the
whole staged-patch hash are pinned. The full JSON report is in a dedicated
temporary directory; recompute before applying. `test-plan.py` rejects 15 unsafe
proposals without touching main or audit inputs.

No new speculative proof is needed for square. After integration, choose the
next easiest remaining actual C jet, reusing the checked infrastructure.
Keep remaining library linkage, environment/evaluator/general-frame/configuration
obligations explicit, not silently treated as complete.

## Avoid repeating diagnosed tool issues

- The real source/config identity checker is `check-jet-source-target.py`
  (`test-jet-source-target.py`), not `check-jets-source-identity.py`. A preparation
  preflight **3895** failed only at that nonexistent path after coverage/static
  checks; corrected checker/test terminal chunk **1f0e23** exited 0 (240 files).
- Snapshot generation is not acceptance; do not use update flags in the full run.
- `review-normal.py --prepare-assumptions` already installed the exact reviewed
  extension; rerunning it must fail, not overwrite a modified snapshot.
- Preserve the existing no-open import for the inherited u128 module and the
  three explicit constructor Print aliases. Do not relax declaration identity.

All-533 goal is active and unfinished. Respect Claude's shared/Elements builder
reservation. Frequent signed atomic local commits only; no push.
