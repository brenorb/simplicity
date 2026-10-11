# Isolated original point-negate acceptance candidate

Candidate `/tmp/jet-gej-negate-accept.5ZRUlU` extends the frozen, reviewed
infinity/predicate candidate `/tmp/jet-predicate-accept.EX7adj`. That baseline's
full acceptance **24487 is still live**, so no baseline acceptance is inferred.
Neither its input files nor the actual checkout proof registry were changed.

Completed source/metadata checks:

- All 34 new Coq modules and two source-gate/test scripts match exact archives.
- All 889 inherited Coq source modules are byte-identical to the baseline.
- Result, definition and coverage inventories strictly extend baseline text.
  Additions: 80 results, 26 definitions, one provisional point-negate entry.
- Supplemental source gate and all 41 mutation fixtures pass on normal candidate
  paths. Coverage tests **71790 exited 0**, including four added point-negate
  rejects for wrong helper/function, wrong contract kind and false premise.
- Candidate coverage metadata reports 354/533, with 250 without an extra
  library premise and 104 conditional on memcpy_model. This is not an accepted
  coverage count. Actual checkout registration remains unchanged.
- All inherited standard snapshots remain unchanged, deliberately. They must
  be extended by actual full generation and reviewed before full acceptance.

`ASSEMBLY.json` records exact baseline/candidate guards for all eight edited
infrastructure files. `assembly-infrastructure.patch` records the actual diff.
Production C/Haskell and proof targets are unchanged. The new source gates
are included in the candidate acceptance script, not merely run manually.

Normal-load-path serial build **91913 is live**, pinned Coq 8.17.1 and 65520 KiB
stack, no scratch overlays. Log `normal-load-path-build.log` at candidate root.
Poll this handle; do not start concurrent compilers or alter its proof inputs.
After it passes, generate full standard snapshots in this separate candidate,
review every inherited/new record against the baseline/preliminary reports,
then run full acceptance with no update/no-build flags. Guard actual checkout
integration against all newer staged/dirty work. No new whole acceptance run
for this candidate has been launched yet.
