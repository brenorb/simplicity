# Actual Bitcoin transaction builder: supporting integration

Freeze source blobs at Claude commit `30404face45383153528f36d915de6d7df11f3f4`.
The root is `C.jet_bitcoin_env_tx_raw`: actual `mallocTransaction` execution,
its copied records and calculated cached hashes, and their connection to
`project_raw_environment`. Review the execution and specification bridge,
not only the pure hash equalities.

Run `python3 -B proof-work/bitcoin-transaction-integration/run.py prepare`,
then `check --candidate DIR`, then `install --candidate DIR`. Use Coq 8.17.1
and `ulimit -s 65520`. Preparation reuses only source-matched, hash-pinned
objects from the previously checked taproot environment unit. Newly added
modules compile; the final kernel check checks the root and its dependencies.
The production AST is regenerated and compared byte-for-byte. Exact theorem
assumptions, untruncated types/definitions, and object/log hashes are retained.

Proofs live under `Coq/bitcoin-env/C`, outside the normal C load path. The
isolated `C.jets_sha` is the environment program, **not** main's original SHA
program. Main's accepted source files and registry/staging remain unchanged.
No coverage is added. Whole-environment composition, startup establishment,
frees, and original-program caller-to-jet transport are later batches.

Premises remain explicit: `memcpy_model`, readable raw structures/buffers and
address bounds, environment-unit SHA dispatch/counter state, and CompCert's
successful allocation semantics. Empty input/output arrays are supported
without requiring their pointers. The raw-environment projection retains
the tap-path bound of 128. The raw transaction ID is copied; this batch does
not compute or validate it. Twelve calculated cache fields are distinguished
from that copied ID. Allocation failure and invalid inputs are not claimed.

`post-check` verifies the imported blobs, checked artifacts, original index,
and exact additive delta from the pre-import input fingerprint. It does not
replace the normal verifier or claim a combined whole-worktree acceptance.
