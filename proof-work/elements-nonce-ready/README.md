# nonce_hash from actual initialization

`Ready.nonce_hash_initial_run` constructs real input/output frames for every
1089-bit logical input, establishes the original Elements SHA dispatch and
counter globals from `Genv.init_mem jets_elements.prog`, and applies the full
`NonceLocal.Actual.nonce_hash_local_spec` theorem. It proves the actual C call
returns the literal option specification's success/failure value, writes its
encoding on success, and preserves every original global load.

`Ready.nonce_hash_initial_execution` additionally proves that the actual
program's initial memory exists. Its only conditional external premise is
the pre-existing `memcpy_model`; no readable-frame, writable-frame, SHA state,
input validity or desired-execution premise remains. Inputs whose compression
count is invalid are included and produce the canonical false return.
The constructed frames are one valid layout for each input; arbitrary valid
layouts are covered by the parent local theorem, not by this existential
corollary alone.

The startup proof is reused unchanged from the kernel-checked
`elements-entropy-ready/Init.v.source`. It describes the same actual Elements
program, not a new implementation. The generic `jet_frames_constructible`
proof is the unchanged source-bound dependency already checked with that
packet. No production C, AST-generation settings, original specification,
API or accepted registry is changed.

Place `Ready.v.source` in a fresh external directory as `Ready.v`. The driver
uses the recorded parent load paths, verifies its twelve inherited external
modules and binds 261 local imports to checked source/object provenance. It
freshly compiles the corollaries and reports both types, their one shared
contract definition and exactly the six inherited CompCert/VST dependencies.

Unregistered proof work: accepted coverage added is zero. Normal admission
and the full repository-wide goal remain unfinished.
