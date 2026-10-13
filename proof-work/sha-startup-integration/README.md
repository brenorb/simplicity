# SHA startup integration

Reviewed source: local Claude commit `30404face45383153528f36d915de6d7df11f3f4`.
Two additional prerequisites are the hash-pinned archived
`jet_clight_forward.v.source` and `jet_sha_initial_globals.v.source`.
The only source transport is `JetStartupReview.` / `JetStartup.` → `C.`.
No skipped proof, unchecked cast, linked memcpy substitution or C change is
included. The old archived global-frame destructuring is not reused: Claude's
restatement matches the current `write_frame_at` predicate.

`stage.py` creates an isolated candidate without changing main. `check.py`
freshly compiles all thirteen new modules and missing inherited dependencies,
checks all 146 result assumption sets, retains fully expanded type/definition
records and independently kernel-checks the complete dependency chains.
`review.py` reconciles exact frozen source transport, inherited main hashes,
compile/report receipts, inventories and kernel context before optional import.
Only import after any in-flight main acceptance audit has terminated.

The supporting batch establishes actual SHA-unit initial memory existence,
dispatch/counter/tag initialization, preservation through caller-owned memory
operations and SHA jet calls, and arbitrary permitted caller lifecycles.
Twenty-one jet contracts carry the invariant from input to output. Tag/output
separation follows from output-frame extent (more than 64 cells), not an added
caller separation assumption. Success and assertion-failure cases are retained.
The existing `memcpy_model` premise remains explicit. Forward-memory and
arbitrary-call determinism results additionally inherit CompCert's two existing
external/inline-assembly semantic-properties assumptions: eight inherited
parameters in the batch, not uniformly six.

The three environment-hash wrappers still use intermediate cached-field
relations (`ext_environment`). They are supporting results; do not replace the
stronger registered raw-canonical environment jet proofs with them. The
constructibility results show satisfiable representations, not actual C
environment-builder execution. This batch does not show that `eval.c` is the
specified lifecycle, does not cover runtime-optimized SHA dispatch, and adds
no newly proved jet to coverage. Normal registry admission is separate.

Main's full Elements-Version acceptance receipt must remain historical to its
frozen inputs after this additive support import. Do not claim that its earlier
fingerprint includes newly imported SHA startup sources. The independent SHA
kernel receipt and source reconciliation are the verification for this batch.

`post-check.py` verifies the exact imported source and proof-object/report
hashes, checks the terminal Version log, and reconstructs its historical input
fingerprint by excluding only these thirteen already-verified additions. It
does not alter the normal audit or claim a new combined full-acceptance run.
It also checks that the original staged patch is unchanged. Three in-memory
fixtures (`test-post-check.py`) reject SHA source, production C and registry
drift. Replay the independent build with `stage.py`, then `check.py --candidate
DIR`; staging permits existing byte-identical support sources.
