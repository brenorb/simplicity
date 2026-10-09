# Integrated frame range correction

The repaired range correction is integrated on `codex/range-integration`.
All 149 changed Coq files match the reviewed reconciliation hashes and the
complete proof-input fingerprint matches the independently accepted candidate.
`RECONCILIATION.json`, `RANGE-CONTRACT-REVIEW.md` and `reconciled-accept.log`
record the scope and evidence. Coverage remains 349/533. Further inherited
endpoint/evaluator/domain/fidelity review is open.

The original 20-commit series remains an exact historical archive. It includes
19 original corrections and the endpoint fix already accepted on the main
topic branch. Replaying only that series reproduces the earlier incomplete
candidate, not the repaired integration.

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
has been checked against the candidate commit. Scoped kernel receipts alone do not
establish acceptance; the later complete acceptance receipt above supersedes
the original stopping point.

Reproduce the separate continuation integrity/replay check without changing
sources or writing Git objects:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 proof-work/range/check-continuation.py /path/to/repaired-candidate
```

This checks each repair against its journal hash, reverse applicability, and
byte-for-byte forward replay from `candidate_commit`. It covers only the
continuation patches, not the original commit-series reconstruction, compiler,
kernel, canonical correspondence, snapshot review or acceptance gates.
