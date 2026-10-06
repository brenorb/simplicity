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

The whole consumer build currently fails at `jet_full_multiply8_layout.v:122`.
The copy and symbolic-executor consumers still use the old separate-block
interface. Prior scoped kernel results do not establish acceptance of the full
candidate. Completing this correction has priority over new jet coverage.
