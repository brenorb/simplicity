# Isolated affine-negate acceptance candidate

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
