# outpoint_hash executions from actual initialization

`Ready.outpoint_hash_initial_run` constructs real frames for every 1375-bit
logical outpoint input, establishes the actual Elements SHA startup state from
`Genv.init_mem jets_elements.prog`, and applies the complete
`OutpointLocal.Actual.outpoint_hash_local_spec` theorem. It derives the actual
C call, canonical option success/failure return, canonical output on success,
output-prefix/cursor properties and preservation of original global loads.

`Ready.outpoint_hash_initial_execution` additionally establishes existence of
that actual initial memory. Its only conditional external premise is the
existing `memcpy_model`; no frame representation, startup state, desired
execution or restricted-input premise remains. Both pegin variants, arbitrary
hash/index values, invalid initial counts and overflow outcomes are included.
These existential corollaries construct one valid layout per input; arbitrary
valid layouts are covered by the parent full-call theorem.

The unchanged generic frame constructor and kernel-checked Elements startup
module are reused. Production code, original specifications, API, generation
settings and accepted registries are unchanged.

Place `Ready.v.source` in a fresh external directory as `Ready.v`. The driver
freshly compiles both results and their contract definition, reports full
types/definitions/assumptions, checks exactly the existing six inherited
CompCert/VST dependencies, verifies twenty-four inherited external modules,
and binds 261 local imports to checked source/object provenance. The explicit
external model remains conditional, not a discharged libc implementation fact.

Unregistered proof work: zero accepted coverage added. Normal admission,
external-library obligations and the broader all-jets goal remain unfinished.
