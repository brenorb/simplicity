# Frame range correction candidate

This exact 20-commit patch series is preserved for review and completion. It is
not applied to the accepted Coq tree and adds no accepted coverage. Nineteen
commits remain unintegrated. The last patch is the endpoint correction already
accepted on the main topic branch; it is included to reproduce the candidate
checkout exactly.

`manifest.json` identifies the base, final candidate commit, original commit
for each patch, source hashes, verification scope and remaining obligations.
Apply the numbered patches in order to an external checkout of `base_commit`.
The final source tree must match `candidate_commit`. The source base remains
reachable from `feat/jet-equivalence`; the original candidate history is also
preserved on `codex/frame-range-contract` in the fork.

The unmodified archived candidate fails at `jet_full_multiply8_layout.v:122`.
This is the original stopping point, not the current continuation state.
`CONTINUATION.md` records the isolated repairs, exact hashes, checked modules,
remaining obligations and live build handles. The additional `*-repair.patch`
files apply after the numbered series; they are not covered by the original
manifest or `proof-work/manage.py` replay. Their separate forward/reverse replay
has been checked against the candidate commit. Scoped kernel receipts do not
establish full candidate acceptance. Completing this correction has priority
over new jet coverage.

Reproduce the separate continuation integrity/replay check without changing
sources or writing Git objects:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 proof-work/range/check-continuation.py /path/to/repaired-candidate
```

This checks each repair against its journal hash, reverse applicability, and
byte-for-byte forward replay from `candidate_commit`. It covers only the
continuation patches, not the original commit-series reconstruction, compiler,
kernel, canonical correspondence, snapshot review or acceptance gates.
