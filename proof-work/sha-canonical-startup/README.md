# Explicit SHA-unit canonical targets over the real startup state

The one new module reuses the existing whole-function execution and startup
proofs for18 still-unregistered jets: SHA compression, ten fixed-size context
additions, buffer511 addition, finalization, TapData initialization, and the
Bitcoin annex/outpoint/tapleaf/tapbranch helpers. The concrete C function,
input/output types and formal program are explicit in each theorem. Compression
names the original `Simplicity.SHA256.hashBlock`, not an opaque replacement.

This does not parameterize an arbitrary Ready predicate. The contracts use
the named `sha_startup_state` established from the actual SHA program's
`Genv.init_mem`, execute in its `sha_ge`, retain output/prefix/cursor/load
observations and re-establish that state. A new nonvacuity theorem exhibits
an actual initial memory satisfying the state. Existing lifecycle and fresh-
frame executability proofs are imported, not assumed or skipped.

Fresh compilation and full declaration/assumption reporting succeeded:
