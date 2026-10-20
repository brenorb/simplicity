# Preserved proof alternatives

Accepted proofs live in `Coq/`. This directory retains distinct earlier proof
sources, diagnostic witnesses, historical patches and alternative approaches.
Nothing here is in the active proof build or adds a registered jet. Older notes
explain those candidates; their development-time counts and pending statuses
are historical. Current status is in `Coq/C/JET_ACCEPTANCE.md` and
`Coq/C/JET_INHERITED_REVIEW.md`.

The `.source` suffix prevents accidental compilation. To work on a candidate,
copy its sources into a fresh external tree, remove that suffix, and use the
namespace in its imports. Some candidates need an older interface or a derived
program tree; do not overwrite the accepted proofs to accommodate them.

The cleanup keeps every distinct Coq source and historical patch. Archived
sources identical to active files were removed; use the active files for those
dependencies. Receipts, source-hash manifests, session inventories and archive
integrity drivers are unnecessary: Git versions the sources, and acceptance is
reproduced with `bash Coq/check-jets.sh --accept`.

For the exact complete archive before cleanup, including original filenames,
namespace/dependency metadata and old patch replay bases, extract the original
revision outside the repository:

```sh
mkdir /tmp/simplicity-original-candidates
git archive c4115d31430537d67724ebbe65d62ce4c2ce1a37 proof-work | \
  tar -x -C /tmp/simplicity-original-candidates
```

This restores historical candidate material, not current acceptance evidence.
The old branches and recovery backups also remain untouched.

Useful groups include:

- `fe-multiply-parallel`: the independent multiplication/square proof, retained
  alongside the selected main proofs; its README gives a reproducible check.
- `range`: the original frame-range patches and subsequent repairs. The original
  series starts at `8f186eef4b513d2e3640a9ba70dabb649ebaeb7e`; apply numbered
  patches in order. This is a historical candidate, not the current accepted tree.
- `secp-field-predicates`: the original predicate candidate patch, based on
  `93542abcf17db8d5b45bdfd7c1e897df39bd3b96`; its reviewed proofs are integrated.
- `review-witnesses`: diagnostics for contract and domain review, some against
  earlier interfaces. These are not additional jet equivalence theorems.
- `derived-trees`: linked-libc and alternate translation-unit or namespace proofs.
- `unbuilt-support`: five known failing support experiments, preserved for repair.
- Scalar, SHA and Elements groups: distinct earlier helper and lifecycle sources;
  many have since been transported into active modules, while others remain
  unaccepted. Consult the active registry before starting duplicate work.
