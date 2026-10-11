# Continue normal scalar-add verification, then reconcile

Current last freshly compiled declaration:
`C.jet_secp_scalar_add_local.scalar_add_literal_local_spec`.
All 24 normal modules / 79 results compile (29824, terminal exit 0).
Types, definitions and exact per-result dependencies match the checked
archives. There is no failing Coq proof goal. Remaining verification is not
an arithmetic/helper/entry/cleanup proof to redo.

## One live handle and a completed kernel check

- **38737**: full scalar-add acceptance, **live**.
  Candidate `/tmp/jet-scalar-add-integration.RxsuOy/Coq`.
  Log `/tmp/jet-scalar-add-integration.RxsuOy/scalar-add-full-acceptance.log`.
  Command `JOBS=1 bash check-jets.sh --accept`, no update/no-build flags.
  Input `951402aa40e88c34b42d24b9bd95725285670df885531ff555b8e290127d5ffc`.
- **10545**: parent scalar normalize/negate acceptance, **terminal exit 0**.
  All gates, 829-module kernel, 4,329 assumptions (2,292 closed) and all four
  ASTs passed with unchanged fingerprint. Post-run pinned review passed.
  `../scalar-integration/ACCEPTANCE.json` is committed as **3bdd03b7**.
  Keep `/tmp/jet-scalar-integration.XAMDsw/Coq` immutable; do not restart it.
- **86561**: terminal **exit 0**, independent normal scalar-add closure kernel check.
  Candidate `/tmp/jet-scalar-add-integration.RxsuOy/Coq`.
  Log `/tmp/jet-scalar-add-integration.RxsuOy/normal-kernel.log`.
  The inherited 15-axiom context matches and all unsafe categories are empty.
  Do not poll or restart this completed check. Its pinned evidence can be
  revalidated with `review-kernel.py`.
  Exact command: `bash build-jets.sh --coqchk -silent -o` followed by
  `C.<name>` for all 24 module names in ASSEMBLY.json. Uses pinned compiler
  and `ulimit -S -s 65520`.

A quiet log does not indicate termination. Poll the existing handles. Do not
change either tree's audit inputs or production C/Haskell. Archive docs and
new, disjoint experiments are not permission to change those inputs.

## On completion

1. Independent kernel terminal success is already recorded in
   `PREPARATION.json`; its log hash is
   `30fac0dd8293d97049546911c0d3fc3f316da314885947d25959bce5fba6c8f3`.
   Revalidate with `review-kernel.py`, preserving candidate sources.
2. Parent **10545** has completed the full terminal/post-run review and its
   signed receipt is present. Original **83287** remains failed evidence.
3. Default `review-normal.py` **without** preliminary/preparation flags passed
   (6372, terminal exit 0). `NORMAL-REVIEW.json` was pinned and is byte-identical
   to the preliminary report. Kernel/fingerprint revalidation also passed.
4. Full scalar-add audit **38737** is already running. Poll it, never launch
   another run or change its frozen inputs. Preserve `AUDIT-RUN.json` and log.
5. On terminal full success, inspect all gates and fingerprint and re-review;
   pin a signed acceptance receipt. This accepts an isolated candidate, not
   main registration. On failure, inspect the first actual diagnostic.
6. Reconcile accepted prerequisites and scalar-add into main: exact sources
   and append-only inventories, reviewed snapshots and gates, preserving the
   staged/unstaged registries and existing SHA work. Do not copy a whole
   scratch tree or .vo/build products into Git. Verify the actual main scope.
   `MAIN-RECONCILIATION.md` and `plan-main.py` record a read-only checkpoint:
   no source conflicts, exact append-only inventories, 5,611 inherited
   contract records and 3,733 dependency records unchanged. Recompute it
   before applying; match full declaration identity/occurrence, not short
   printed names. `test-plan.py` checks duplicate and qualified-name cases.

## Reproduce read-only checks from main

```sh
python3 -B proof-work/scalar-add-integration/review-normal.py
python3 -B proof-work/scalar-add-integration/test-review.py
python3 -B proof-work/scalar-add-integration/review-kernel.py
python3 -B proof-work/scalar-add-integration/test-kernel.py
```

`assemble-candidate.py --verify` is an **initial preparation** check requiring
inherited snapshots unchanged. It correctly rejects a later reviewed
snapshot extension; use the pinned normal reviewer after preparation.
Do not rerun the assembler on either audited tree.

The original AddC archive remains independently kernel-checked. The normal
candidate inherited all old contract bytes; no print-context rewrite of the
inherited snapshot was accepted. Deep prints reproduce the exact standard
driver's full import context, not merely the new module imports.

All-533 goal is active and unfinished. Main coverage 351/533; isolated
359/533 is provisional. Scope is local frames / LP64 / RECKLESS, not all
evaluator frames or assertion-enabled builds. Leave Claude's Elements,
memcpy/linkage, SHA startup and constructibility modules/registries alone.
Signed local atomic commits; never push.

Disjoint next-jet helper progress is in `../scalar-mul`: 17 actual unsigned
multiplication / struct-wrapper results compile and pass independent kernel,
type/definition/dependency review. No public multiply/square proof or extra
coverage is claimed. Continue there while this audit runs, without editing
the audited candidate.

Further checked progress: `../scalar-mul-accum` (11 results, signed
**9fd37502**) proves actual multiply-accumulate and the modulo-128-bit value.
`../scalar-mul512` adds 19 results: a sound compact no-op-conditional executor
and actual original scalar_mul_512 entry/calls/cleanup/output representation.
All compile and pass independent kernel/type/dependency review. The full
numeric product and public multiply/square equivalences remain open. Read
that archive's diagnosed no-op-branch duplication before replaying a full
symbolic tree reduction. Audit **38737** has passed kernel on 853 modules and
is now at the assumption gate; still not terminal acceptance.
