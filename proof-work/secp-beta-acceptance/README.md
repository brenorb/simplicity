# Multiplication and beta registration attempt

This is a **failed normal registration attempt**, not accepted coverage.
The isolated candidate is `/private/tmp/jet-beta-acceptance-hv9w3y53`.
It combines the separately checked ordinary multiplication and beta proof
closures without changing the production implementation or frozen specifications.

The candidate contains 351 entries: the existing 349, field multiplication,
and multiplication by beta. That number describes candidate metadata only.
No entries were promoted to the main registry by this attempt.

The unchanged normal command, `bash check-jets.sh --update-expected`, terminated
with exit status 1. The coverage fixtures and multiplication/beta source-review
gates passed, including 22 beta mutation tests. The next gate failed with
`Bitcoin base primitive name mismatch: LockTime`.

This is the previously reported frozen identity discrepancy: original Coq uses
`locktime`, whereas the original Haskell commitment name is `lockTime`.
See the separately checked counterexamples in `../bitcoin-frozen-identity`.
The normal workflow did not reach its compilation, recursive kernel audit,
snapshot review, or acceptance stages. The separately checked proof packets
do not make this failed normal run successful. There is no `GENERATED.json`,
`REVIEWED.json`, or `ACCEPTED.json` receipt here.

`GENERATION-FAILED.json` binds the actual terminal process, complete
`generate-failed.log`, and unchanged non-snapshot inputs. Accepted coverage
added is zero. Do not rerun the unchanged failing gate to claim new progress,
bypass the identity check, or alter the frozen primitive to obtain acceptance.

## Preparation bookkeeping correction

The initial preparation recorded the correct final candidate hashes, but
sampled the `before` value too late for ten newly materialized sources and
the two project files. The original preparation, driver, and candidate were
preserved. `materialization.py` and `MATERIALIZATION.json` add an independently
recomputed checked-parent-to-candidate delta for precisely those twelve paths;
the runner verifies it before running generation. This corrects an observation,
not a proof or source target, and does not retroactively rewrite a receipt.
