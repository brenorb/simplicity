# Entropy jet: real startup and fresh-frame execution

`entropy_startup_initialized` establishes both the SHA compression dispatch
pointer and maximum-counter value from `Genv.init_mem jets_elements.prog`.
The actual original program's initializers are checked by a proved Boolean
checker, establishing that an initial memory exists.

`calculate_issuance_entropy_initial_run` constructs input and output frames
for every `((Word256, Word32), Word256)` input, preserves all initial global
loads, invokes the complete original C jet, and obtains the exact canonical
Simplicity output. Neither represented-frame nor startup premises remain.
`calculate_issuance_entropy_initial_execution` also chooses the initial memory
using the existence theorem: its only conditional library premise is the
existing explicit `memcpy_model`.

These are corollaries of the arbitrary valid frame/cursor/output-content
theorem, not a replacement restricted-layout equivalence. Their fresh-frame
allocation is existential, while the parent theorem covers callers' existing
valid layouts. No real allocator, evaluator integration, libc linkage or
production executable initialization outside the modeled Clight program is
claimed here.

`Init.v.source` reuses the generic initializer reasoning already checked for
the three calculation jets and adds the actual maximum-counter initializer.
`Ready.v.source` composes the unchanged shared frame-constructibility theorem
with the entropy local specification. The Coq proof-engineering skill guided
these explicit, separately discharged interfaces.
