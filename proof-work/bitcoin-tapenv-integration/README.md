# Actual Bitcoin taproot builder: reviewed support batch

This batch is frozen from Claude commit
`30404face45383153528f36d915de6d7df11f3f4`. Nineteen derived-unit modules cover
the actual `simplicity_bitcoin_mallocTapEnv`, the tapleaf/path/environment hash
links, logical-environment description, and the link to
`project_raw_environment`. It includes the streaming SHA-to-byteStringHash
bridge needed by the raw-data result. No registered jet theorem is replaced.

`stage.py` makes an isolated derived C namespace. Only modules unaffected by
the changed SHA program may reuse copies of compiled objects; all program-
dependent SHA and builder modules are recompiled for the real environment
unit. No compiler output is symlinked into main. `check.py` regenerates the
AST from production C, builds the closure, checks every new result's exact
dependencies, retains untruncated types/definitions, and kernel-checks all
three roots with their dependencies. `review.py` reconciles immutable Git
blobs, inherited main sources and the terminal receipts before importing only
new files. Never import during main's in-flight acceptance audit.

Program boundary: in the isolated tree `C.jets_sha` contains the generated
`jets_bitcoin_env.v`, not main's original SHA unit. The durable proof sources
are stored in `Coq/bitcoin-env/C`, outside the normal C namespace. Do not load
them against main's original `C.jets_sha` or claim original-program caller/jet
composition without transport. The current import is supporting verification,
not new jet coverage or normal registry admission.

`mallocTapEnv_raw_cached_hashes` includes the actual Clight call, a fresh
returned block, all three canonical cached hash arrays and preservation of
old memory. It retains explicit `memcpy_model`, readable raw-data/array/address
conditions, the path-length bound of 128, and SHA dispatch/counter/tag startup
premises. The latter need establishment for this distinct environment unit;
the prior startup theorem for the original SHA unit is not silently reused.
CompCert's successful malloc model does not cover system allocation failure.
Invalid/null raw arguments and excessive paths are not claimed by this result.

The environment AST also contains transaction/build_txEnv functions, but this
batch does not claim their proofs. Actual transaction builders, whole txEnv
composition, frees and evaluator integration remain subsequent batches.

After import, `post-check.py` verifies all caller source/object/report hashes,
the terminal getter receipt, the unchanged staged patch and the prior complete
input fingerprint with only these exact checked additions excluded. It does
not alter the normal verifier or claim a new whole-worktree acceptance run.
`test-post-check.py` rejects three in-memory source/production/registry changes.
Replay this supporting audit with `stage.py`, then `check.py --candidate DIR`.
