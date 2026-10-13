# Continue the same full scalar-multiply acceptance run

## Terminal success supersedes the historical launch notes below

Full acceptance **38093** terminated with exit 0 (terminal chunk **c92c32**).
All gates passed: normal build, 922-module kernel, 4,767 assumption records
(2,635 closed), reviewed type/definition snapshots, negative tests and all four
regenerated AST comparisons. The frozen fingerprint is unchanged. Post-run
review and mutation tests **67725** also terminated with exit 0. `ACCEPTANCE.json`
pins the terminal log and exact scope. Do not poll or restart either completed run.

Isolated **360/533** coverage is now accepted (256 entries without an extra
library premise, 104 explicitly memcpy_model-conditional). Main remains
separate at 351/533; no main registration is implied. The next integration
step is exact main reconciliation below, preserving dirty index/worktree work.
Keep the accepted candidate immutable. `AUDIT-RUN.json` remains historical
launch evidence, not the final receipt.

Actual handle **38093** was verified live at the last observation, running
`check-jets.sh --accept` in
`/tmp/jet-scalar-multiply-integration.yIS07H/Coq`.
Log: `/tmp/jet-scalar-multiply-integration.yIS07H/full-acceptance.log`.
The command is in `AUDIT-RUN.json`; it uses a 10,800-second process bound,
not a tool output-yield interval. Static/source/literal/negative tests and
the build completed; the last phase was whole-registry `coqchk`.

First poll **that same handle**. Observation timeout or no new text does not
mean the run stopped. If the handle is genuinely missing, inspect the owned
process/terminal state and log; do not launch a duplicate merely from intent,
a state file or an old log. Do not modify any candidate input while it runs.

## Evidence already terminal-successful

- Normal build: **19523**, exit 0; exact namespace-transported closure.
- New dependency driver: **72404**, exit 0; 359 results, 292 closed.
- Deep contract driver: **56568**, exit 0; 676,351 bytes, untruncated.
- Contract snapshot generation: **30848**, exit 0; preparation only.
- Independent normal kernel: **45365**, exit 0, inherited context/unsafe checks.
- Full normal snapshot review: **28330**, exit 0; all 6,596 inherited records
  byte-identical, all 4,408 inherited assumption entries preserved, exact new
  source/type/definition/dependency reconciliation.
- 11 normal-review and five public-boundary corruption fixtures passed in
  memory; coverage/static/source identity preflights passed.

`PREPARATION.json`, `ASSEMBLY.json` and `NORMAL-REVIEW.json` describe these
checks. None of them is full acceptance or main-checkout registration.
Frozen preacceptance fingerprint:
`1b159005caeac45684fe3b38d56f46bd78a166845fa62fc365137cafe82c3669`.

## After terminal acceptance

On exit 0, verify the log includes all acceptance gates and all four AST
comparisons, and verify the fingerprint is unchanged. Re-run normal review
and in-memory tests. Record the actual terminal result, log hash, kernel/module
and theorem counts and exact coverage in a new `ACCEPTANCE.json`. Only then
describe candidate 360/533 as accepted isolated coverage; main remains separate.

On a genuine failure, preserve the terminal status and diagnose its first
failing gate before changing anything. Do not weaken a type/definition/axiom
gate, skip a build, omit an AST comparison, or accept snapshots automatically.

Then reconcile the accepted candidate into main, preserving staged/unstaged
registry/range/SHA/field-negate work. The scalar-add parent is also not yet
integrated into main, so compare against actual current sources and inventories,
not old intended plans. Reuse `review-normal.py`'s ordered record parser for
the three known constructor-parent Print cases and duplicate printed names;
the older scalar-add reconciliation parser does not know those constructors.
The new read-only `plan-main.py` does this; `MAIN-RECONCILIATION.md` records
its latest checkpoint (270 source additions, no source conflict, inherited
contracts/dependencies unchanged, four gate scripts requiring explicit review).
Recompute its full output against the current worktree and index before applying.
Report exact overlaps before changing conflicting user work. Verify the final
main tree with full acceptance before updating its accepted coverage.

Square's shared-input-pointer proof remains next, as described in
`../scalar-multiply-public/CONTINUATION.md`; do not duplicate owned regions.
Claude's shared/Elements reservations are unaffected. Keep the complete
all-533-jet goal active. Frequent signed atomic local commits; never push.
