# Finish square acceptance, then reconcile cumulative main work

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
