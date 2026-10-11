# Isolated affine-negate acceptance candidate

Candidate `/tmp/jet-ge-negate-accept.5mtyZa` extends the frozen point-negate
candidate `/tmp/jet-gej-negate-accept.5ZRUlU`. The point candidate's full
acceptance **77601 remains live**; no baseline acceptance is inferred here.
Neither its inputs nor the actual dirty checkout registry were changed.

Assembly verification passed: 923 inherited C-namespace Coq sources byte-identical,
38 new proof modules and two source-check scripts hash-identical to archives,
eight strictly scoped infrastructure changes, 109 result/37 definition rows
and one provisional affine coverage row appended. Both inherited snapshots
remain byte-identical, intentionally: actual generation follows the build.
Reproduce the read-only guards with `assemble-candidate.py --verify`.
Supplemental whole-project guards also check all 948 inherited `.v` sources,
including the canonical Simplicity modules, and reject extra candidate modules.

The source gate and 53 negative fixtures passed; coverage tests **63462
exited 0**, including four new affine wrong-function/helper/contract/premise
rejections. Candidate metadata reports 355/533, including 104 contracts still
conditional on `memcpy_model`. This is not accepted checkout coverage.

Normal-load-path serial build **96488 is live**, pinned Coq 8.17.1,
65520 KiB stack, no scratch overlays. Log at candidate root:
`normal-load-path-build.log`. Do not alter inputs or launch another compiler.
Only after terminal success: generate the full contract and axiom snapshots,
reconcile every inherited/new record against baseline and reviewed reports,
then launch full acceptance without bypass/update flags. Archive the result
before proposing guarded integration around the newer staged/dirty changes.
