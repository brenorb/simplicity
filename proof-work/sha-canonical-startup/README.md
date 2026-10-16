# Explicit SHA-unit canonical targets over the real startup state

Private tree: `/private/tmp/jet-sha-canonical-startup.8SBgLe7u`, cloned from
the completed inputs proof tree, never from a running audit's objects.
Main420 inputs and the original staged patch remain unchanged.

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

```sh
python3 -B proof-work/sha-canonical-startup/check.py /private/tmp/jet-sha-canonical-startup.8SBgLe7u
```

`RUN.json` binds19 results and no new definitions, including the nonvacuity
result with four inherited foundational assumptions. Nine inherited startup
support modules were freshly rebuilt before the adapter. Each of the18 C
endpoints has **eight**, not six, inherited assumptions: keeping the global
state also uses CompCert's existing external/inline-assembly semantic-properties
parameters. The explicit `memcpy_model` premise is preserved for17 endpoints;
only the compression endpoint has no extra libc premise. No new axiom or
allowlist change is made.

The once-only recursive kernel/SHA-AST controller is running under handle5964;
`KERNEL-RUN.json` binds its actual launch. Poll that existing handle, preserve
the private source/object tree and do not restart from silence or a missing
terminal receipt. Canonical-source/transitive-port review, independent
evidence review and normal admission remain. These are adapters
of existing execution proofs, not18 new execution derivations. No extra
coverage, full acceptance, runtime-optimized dispatch support or completion of
the every-jet goal is claimed. Eventual registration must include the startup
support dependency closure; source files being present is not build coverage.
