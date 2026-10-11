# Accepted normal scalar baseline — continue scalar-add/main integration

The all-533 goal is active, unfinished and not blocked. The complete public
scalar-normalize/negate contracts and their exact 25-module normal C closure
have now passed full acceptance. No caller proof needs to be redone.

## Terminal acceptance, not a live process

**10545** terminated with **exit 0**, using `JOBS=1 bash check-jets.sh --accept`
without update/no-build flags, in `/tmp/jet-scalar-integration.XAMDsw/Coq`.
Do not poll or restart it. `ACCEPTANCE.json` pins the terminal receipt:

- Log `/tmp/jet-scalar-integration.XAMDsw/scalar-integration-full-acceptance-retry.log`.
- Log SHA-256 `5d22cbc4ce4afb1111110b8c7b5d9cc79b747f2c077666941599b597bcd1381a`.
- Unchanged input `aa652e53f690b80bcdc03a263f11114d04b1e9743f3dac471a41b00e9dac42ec`.
- Build, 829-module kernel, 4,329-result assumption comparison (2,292 closed),
  exact public types/definitions, negative gates and all four ASTs passed.
- Post-run pinned normal review passed; inherited sources/contracts/axioms,
  all new source/type/definition/dependency evidence remained unchanged.

Original **83287** failed with exit 2 at missing sibling source layout and
remains failed evidence. Only the retry is accepted. Its repaired read-only
`C`/`Haskell` source links match the accepted parent's layout. Keep this
accepted candidate immutable; scalar-add was prepared without modifying it.

## Next

1. Scalar-add's default normal review now succeeds with this terminal parent
   receipt; its source/snapshot report exactly matches the preliminary one.
   See `../scalar-add-integration/CONTINUATION.md` for its current full audit.
2. After scalar-add full acceptance, reconcile accepted prerequisites and
   scalar-add into the dirty main checkout. Preserve mixed staged/unstaged
   inventories, SHA-support work and main-only experiments. Read-only
   `../scalar-add-integration/plan-main.py` found no source conflicts and
   exact inherited contract/dependency preservation. Recompute before writes.
3. Verify actual main scope separately; isolated acceptance is not main
   registration. Do not copy whole trees or .vo/build outputs into Git.
4. `../scalar-mul` has 17 newly compiled/kernel-checked actual multiplication
   helper results and exact evidence. Continue from the original-C helper
   contracts toward literal public multiply/square specs, not assumed calls.

Reproduce read-only review from main:

```sh
python3 -B proof-work/scalar-integration/review-normal.py
python3 -B proof-work/scalar-integration/test-review.py
```

`assemble-candidate.py --verify` remains an initial preparation check and
must reject reviewed snapshot extensions; do not rerun the assembler.

Accepted isolated coverage **358/533**, main **351/533**. Local-frame / LP64 /
RECKLESS scope remains; evaluator-wide/all-frame and assertion-enabled
obligations are not discharged. Claude owns Elements/shared linkage/startup/
constructibility; no overlap. Signed local atomic commits, no pushes.
