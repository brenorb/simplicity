# Archived derived proof trees

These seven trees used to live under `Coq/`. They are **not** built by
`Coq/check-jets.sh` and are not counted in `jet_coverage.tsv`. Each file has its
original path and SHA-256 in `manifest.json`. Coq sources and scripts carry a
`.source` suffix, so nothing here is compiled or run by accident.

| Tree | Modules | What it proves |
| ---: | ---: | --- |
| `linked` | 16 | Core and SHA programs with the reference `memcpy` linked internally, plus CompCert linking theorems. Discharges `memcpy_model` for a *linked* program; the unchanged program's 104 conditional entries stay conditional |
| `bitcoin-env-linked` | 2 | The same, for the Bitcoin environment unit |
| `bitcoin-env` | 55 | SHA-unit proofs recompiled against the Bitcoin environment translation unit (`C.jets_sha` := `C.jets_bitcoin_env`), environment readiness and startup |
| `elements-env` | 56 | Elements environment helpers and callers (taproot setup, copyOutput, confidential/issuance hashing, fees) |
| `elements-sha` | 11 | SHA proofs in the Elements program; annex/tapleaf/tapbranch |
| `startup` | 9 | SHA startup invariant, in the older `JetStartup` namespace (the `C.jet_sha_startup_*` modules in `Coq/C` are the transported versions) |
| `forward` | 3 | Forward-memory issuance-token helpers, in the older `JetForward` namespace |

## Why they are archived

Each derived tree needs a copy of `Coq/C` with one program module substituted,
which the ordinary project cannot express. They were built and kernel-checked
only by copied-tree drivers in `proof-work` (`linked-repair`,
`claude-remainder-integration`), and those drivers depended on run receipts.
Receipts and drivers were removed (`Coq/AGENTS.md`: evidence is the commit
plus one reproducible command), so these trees currently have no build path.

## Restoring one

1. Extract the files to their `original_path` (or a scratch tree).
2. Write a build that copies `Coq/C`, substitutes the program module, and
   compiles the tree with `build-jets.sh` flags. The pre-integration scripts
   `Coq/build-{linked,bitcoin-env,elements-env,elements-sha,startup}.sh` on
   branch `claude/shared-obligations` show each substitution.
3. Wire that build into `check-jets.sh` before registering anything that
   depends on it.
