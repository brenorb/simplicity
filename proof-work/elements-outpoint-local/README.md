# Complete original Elements outpoint_hash equivalence

`Actual.outpoint_hash_local_spec` proves the actual original
`jets_elements.f_simplicity_outpoint_hash` call in `elements_ge` against the
literal `Spec.elements_outpoint_hash_spec`, interpreted in `optalg`.
It includes entry, source-frame copying, real SHA initialization and context
parsing, both pegin branches, the hash/index bytes, output writing, return-value
conversion and freeing every actual local. This is implementation-to-specification
equivalence, not merely a byte-stream or mathematical specification lemma.

The input is 1375 bits and the output context is 830 bits. Both pegin variants,
all hash/index values and arbitrary valid frame cursors, boundary crossings and
pre-existing output bits are covered. Invalid initial counts and final overflow
return false as required by the canonical option semantics. Success writes the
canonical encoding, preserves preceding output bits, updates the output cursor
and preserves loads outside the permitted output ranges.

Explicit conditional boundaries remain the existing `memcpy_model`, the actual
Elements SHA dispatch/maximum-counter loads, and ordinary readable-input /
writable-output frame representations. No desired call, intermediate context
or output is assumed. Initial-memory/frame construction is a separate next
corollary; this packet alone does not claim those premises are inhabited.

## Original target and reuse

`Spec` retains the literal original Elements routing: annexHash on the optional
pegin, then ctx8Add32 on the hash, then ctx8Add4 on the index. It uses the existing
kernel-checked `AssetLocal.Buffer` and `AssetLocal.ContextHashes` pure modules,
including the literal annexHash definition. `SOURCE-REVIEW.json` binds the
original Haskell type, routing, annex dependency, width helpers, selectors,
catalog binding, C body and all five new proof sources. This explicit literal
source review is not a formal Haskell translation theorem.

The existing outpoint call and middle proofs supply actual C execution in its
original order: present pegin data is read before its prefix-byte absorption.
`Bridges` adapts the checked frame copy to `op_env`, checks the actual entry and
free list, and retains the real 16/32/36/88-byte local layout. The 32-byte midstate
is not confused with the 36-byte scratch array; the result temporary is `_t'3`.

The generic sticky-overflow proof is reused unchanged from the asset packet.
Its new specialization normalizes 37/69-byte processing while covering a
maximum-counter crossing at an intermediate step. No input is excluded to
avoid failure. No production implementation, original specification, API or
generation setting is changed.

## Verification

```sh
python3 -B proof-work/elements-outpoint-local/verify.py compile EXTERNAL_DIRECTORY
python3 -B proof-work/elements-outpoint-local/verify.py kernel EXTERNAL_DIRECTORY
```

Place the five archives in a fresh external directory as `Spec.v`, `Counter.v`,
`Bridges.v`, `Local.v`, `Actual.v`. The driver freshly compiles them, reports full
types/definitions/assumptions, checks exactly twelve results and three
definitions, binds 260 local imports to forced source/object provenance and
checks eighteen inherited external modules. Eight new results are closed;
the global-state equivalence has four inherited dependencies; the source-copy
and two full-call theorems have the existing six CompCert/VST dependencies.
The external memcpy model remains a premise, not a discharged libc fact.

`RUN.json` records compilation, `KERNEL-RUN.json` only a launch. Only successful
`CHECKED.json` with kernel exit status zero records completed recursive kernel
checking for the exact bound inputs. The full audit checks its entire dependency
chain even if a separate middle audit is still running. Preserve bound sources,
objects, review and driver while an audit is live; poll the existing process.

Unregistered proof work: accepted coverage added is zero. Normal admission,
external-library obligations and the full all-jets goal remain unfinished.
