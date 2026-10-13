# Nullable tappath: normal registry admission

The existing `simplicity_bitcoin_tappath` coverage row is migrated from
`C.jet_bitcoin_raw_jets.bitcoin_tappath_raw_local_spec` to
`C.jet_bitcoin_tappath_nullable_raw.bitcoin_tappath_nullable_raw_local_spec`.
This is a domain improvement for the same original C function and canonical
raw primitive: an empty path no longer requires an unused path-pointer load.
Nonempty paths retain the same relation; the old module and theorem remain
available. The inherited tap-path-length bound of 128 is unchanged.

## Reviewed delta

The normal manifests add two modules, nine public results and one contract
definition. All 7,299 inherited contract records remain byte-identical and
ordered; all 4,814 inherited result dependency sets remain unchanged. The nine
new dependency sets exactly match the prior whole-dependency independent
kernel check. The normal printer truncates two long new records, so the
candidate also retains fully expanded records, with every compact fragment
checked against them. No statement, definition or proof is skipped.

Eight corruption fixtures operate only in memory. They reject changes to
coverage, inventories, inherited types, dependency sets and deep records.
No production C, canonical specification, generated program, existing proof
or external-library condition is changed. Coverage remains 361/533.

The isolated candidate is `/tmp/jet-nullable-admission.k3nw6pma`; preparation
is not acceptance. An initially redundant whole-registry snapshot-preparation
run (35931) was stopped, with its exact three owned processes identified.
`prepare.py` prints only the additions in the full gate's import context and
merges them with unchanged inherited records. Full acceptance still checks
the entire registry; this avoids doing that expensive traversal twice.

## Installation and acceptance

`review.py --apply` installs only the seven reviewed metadata/snapshot deltas
into the actual main worktree. It checks original file hashes, preserves every
existing proof and leaves the index unchanged. This is intentionally a
worktree-only change: committing these whole dirty metadata files would also
commit unrelated preexisting staged/unstaged work.

Full actual-main acceptance is run once, without update/no-build flags. Its
frozen input fingerprint is
`7223f862a6ae78fd2763b0cca414fb494e6cf3c8b22a213c2a533f0648ee09fd`.
`AUDIT-RUN.json` identifies the process and log; a running process is not
acceptance. `ACCEPTANCE.json`, when present, records terminal success, log
hash and unchanged inputs. Keep main Coq sources, registries, C and Haskell
inputs frozen until that process completes.

```sh
python3 -B proof-work/nullable-admission/post-check.py
```

`post-check.py` verifies installed metadata, exact preexisting index hashes,
the staged patch and frozen source fingerprint. It reports acceptance only
when a valid terminal receipt exists. `assemble.py`, `prepare.py`, `review.py`
and `test-review.py` reproduce the pre-installation candidate workflow; they
must not be rerun as though the now-migrated main registry were the old base.

Local signed commits preserve the imported sources and the admission tooling/
evidence. Main's preexisting index is not rearranged to force an unrelated
registry commit. Nothing is pushed, and this milestone neither resumes nor
completes the paused all-jet app goal.
