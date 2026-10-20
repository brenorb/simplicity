# Actual Bitcoin transaction builder: supporting integration

Freeze source blobs at Claude commit `30404face45383153528f36d915de6d7df11f3f4`.
The root is `C.jet_bitcoin_env_tx_raw`: actual `mallocTransaction` execution,
its copied records and calculated cached hashes, and their connection to
`project_raw_environment`. Review the execution and specification bridge,
not only the pure hash equalities.

Proofs live under `Coq/bitcoin-env/C`, outside the normal C load path. The
isolated `C.jets_sha` is the environment program, **not** main's original SHA
program. Main's accepted source files and registry/staging remain unchanged.
No coverage is added. Whole-environment composition, startup establishment,
frees, and original-program caller-to-jet transport are later batches.

Premises remain explicit: `memcpy_model`, readable raw structures/buffers and
address bounds, environment-unit SHA dispatch/counter state, and CompCert's
successful allocation semantics. The C execution theorem supports empty
input/output arrays without requiring their pointers. The specification
bridge uses Bitcoin's existing environment type, whose transaction requires
at least one input; it does not represent zero-input environments.
The raw-environment projection retains
the tap-path bound of 128. The raw transaction ID is copied; this batch does
not compute or validate it. Twelve calculated cache fields are distinguished
from that copied ID. Allocation failure and invalid inputs are not claimed.
The current `raw_buffer_at` relation also requires a valid, non-null data
block even for an empty script/annex buffer. Null empty buffers are therefore
outside this batch's contract, distinct from the covered null empty arrays;
relaxing that representation premise is a subsequent generalization.

`post-check` verifies the imported blobs, checked artifacts, original index,
and exact additive delta from the pre-import input fingerprint. It does not
replace the normal verifier or claim a combined whole-worktree acceptance.

Verification completed for 43 derived builder modules (26 new source files),
407 theorem/lemma reports and 161 definition records: build, production AST
regeneration, report checks, and full dependency kernel check all exited 0.
247 reported results are closed; all remaining reported results stay within
the six reviewed inherited dependencies. No new axiom or unchecked cast was
introduced. Evidence and the exact additive preservation record are retained
in this directory's JSON receipts; detailed checker logs and objects are
hash-pinned in the isolated candidate named there.
