# Preserve the live normal scalar acceptance

The all-533-jet goal is active, unfinished and not blocked. There is no new
scalar caller proof to redo: both complete public local theorems and their
exact 25-module normal-C closure compiled, with all new/inherited snapshot
boundaries reviewed. The three getter modules were the missing dependency
in the older 22-module estimate; do not revert that correction.

## Live process

**10545** owns the full acceptance retry in
`/tmp/jet-scalar-integration.XAMDsw/Coq`:

```sh
export PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH
export JET_C_REPO=/Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity
ulimit -S -s 65520
JOBS=1 bash check-jets.sh --accept \
  > /tmp/jet-scalar-integration.XAMDsw/scalar-integration-full-acceptance-retry.log 2>&1
```

Poll this same session and inspect its log. A quiet run is not failure and
does not justify restarting. Do not mutate sources, gates, project/result/
definition/coverage inventories, snapshots or production C/Haskell inputs.
Input fingerprint:
`aa652e53f690b80bcdc03a263f11114d04b1e9743f3dac471a41b00e9dac42ec`.

Session **83287** is terminal, exit **2**. Its original log is preserved.
All proof gates passed; AST preprocessing failed on missing `../../C/frame.c`.
The candidate had copied only `Coq`, unlike its accepted parent with sibling
`C` / `Haskell` links. Those read-only links are now restored, normal review
passed unchanged (40956, exit 0), and core AST regeneration passed. Neither
partial gates nor this preflight authorize acceptance. For future candidate
preparation, preserve the parent's sibling source layout and verify source
links before launching a long audit. Do not restart **10545**.

The previous scalar-zero process **45608** is terminal, exit **0**, with its
fully reviewed receipt now in `../scalar-zero/ACCEPTANCE.json`. Do not wait
for or restart it. Its accepted immutable baseline remains unchanged.

## On terminal completion

1. On failure, inspect the first actual diagnostic and determine its source;
   never weaken a statement, add an execution/output/free premise, broaden
   axioms, or silently update expected snapshots.
2. On exit 0, review the entire final log: build, kernel, exact assumption and
   contract comparisons, negative gates and all four AST matches. Recompute
   the source fingerprint and require it equal the initial value. Re-run
   `python3 -B proof-work/scalar-integration/review-normal.py`; all hashes and
   pinned source/evidence/definition/dependency records must match.
3. Only then create a signed local `ACCEPTANCE.json` receipt. Provisional
   358/533 becomes accepted **isolated** coverage, not main registration.
4. Reconcile the accepted closure into the main checkout, preserving the
   mixed staged/unstaged registry changes and existing SHA-support work.
   Integration includes the earlier field/point/affine/scalar-zero accepted
   prerequisites. Use immutable receipts/source manifests, do not copy a
   whole scratch tree or generated build products into Git. Verify main
   coverage and snapshots after exact source/inventory reconciliation.
5. Continue easiest remaining scalar/other jets, reusing the proved actual
   reader, serializer, owned-lifecycle and literal-program interfaces. Each
   new jet still needs its own original C arithmetic and literal spec bridge.

## Reproducible read-only checks

From the main checkout:

```sh
python3 -B proof-work/scalar-integration/review-normal.py
python3 -B proof-work/scalar-integration/test-review.py
```

`assemble-candidate.py --verify` is deliberately an **initial preparation**
check: it requires inherited snapshots unchanged. It must reject the current
reviewed snapshot extension. Use the pinned normal reviewer after preparation;
do not bypass that distinction or rerun the assembler on the live candidate.

Scope remains local-frame / LP64 / RECKLESS, not full evaluator/all-frame or
assertion-enabled execution. Claude owns shared linkage/startup/constructibility
and Elements foundations; leave its worktree/modules untouched and write its
COORDINATION.md only if an actual overlap arises. No remote pushes.
