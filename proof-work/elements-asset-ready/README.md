# asset_amount_hash executions from actual initialization

`Ready.asset_amount_hash_initial_run` constructs real frames for every 1346-bit
logical input, establishes the original Elements SHA dispatch/counter globals
from actual `Genv.init_mem jets_elements.prog`, and applies the complete
`AssetLocal.Actual.asset_amount_hash_local_spec` theorem. It derives the real
C call, canonical option success/failure return, canonical output encoding on
success, output-prefix/cursor properties and preservation of original globals.

`Ready.asset_amount_hash_initial_execution` also establishes existence of that
actual initial memory. Its only conditional external premise is the existing
`memcpy_model`; no represented frame, startup state, intermediate execution or
restricted-input premise remains. Invalid context counts and overflow outcomes
are included. These corollaries construct one valid frame layout per input;
arbitrary valid layouts are covered by the parent local theorem.

The generic frame construction and unchanged startup module are reused from
the kernel-checked entropy initialization packet, which concerns the same
original Elements program. Production code, original specifications, API,
generation settings and accepted registries are unchanged.

Place `Ready.v.source` in a fresh external directory as `Ready.v`. The driver
freshly compiles both results and their contract definition, reports full
types/definitions/assumptions, checks exactly the six inherited CompCert/VST
dependencies, verifies twenty-five inherited external modules, and binds 261
local imports to their checked source/object provenance. The explicit external
model remains a premise, not a discharged libc implementation fact.

Unregistered proof work: accepted coverage added is zero. Normal admission,
remaining external-library obligations and the full all-jets goal are unfinished.
