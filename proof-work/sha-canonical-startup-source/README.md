# Canonical-source review for the explicit SHA startup contracts

The formal implementation-to-program proofs are the18 whole-C endpoints in
`../sha-canonical-startup/`; their actual recursive kernel/SHA-AST check has
completed. This source review checks the particular canonical programs those
proofs name. It is not a substitute for the formal C execution proofs and does
not register jets, prove host libraries or claim every-jet completion.

The fixed model checks148 Coq declarations/statements,22 selected Haskell
blocks,74 routing/type/helper/import records, three complete wrapper/type
modules and19 complete C function bodies (18 endpoints plus the shared
fixed-size addition helper). It includes all19 public theorem statements,
the whole startup total/partial contracts and the named startup-state
definitions. There is no arbitrary caller-chosen Ready predicate.

## Reviewed correspondence

| Canonical source | Formal target and significant details |
| --- | --- |
| `Sha256.lib.hashBlock` | Original `Simplicity.SHA256.hashBlock`: same round/schedule/projection tree, rotations, shifts, bitwise operations and final collation. All64 constants are independently compared as hex vs decimal, including the first round. |
| `mkLibAssert.ctx8Add1` | Buffer snoc, carry assertion, compression, then verification of the resulting count. The exact pruned-branch hash and count-assertion program are retained. |
| `ctx8Addn` | Single-vector base and left-half-then-right-half recursion. Ten catalog widths correspond to vector depths0 through9 over bytes. |
| `ctx8AddBuffer buffer511` | Single-buffer empty/present branches, including verification when empty, and recursive buffer-vector absorption. Buffer depth8 is511 bytes, not512. |
| `ctx8Finalize` | Verify then clear the counter for padding; append the big-endian2^63 word, pad the remaining buffer, and form the final block with the original bit length. Positive shifts6 and3 are retained. |
| `tapdataInit` | Empty63-byte buffer, counter1, and the midstate after two copies of SHA256 of the seven ASCII bytes `TapData`. |
| `Bitcoin.annexHash/outpointHash` | Absent/present0/1 marker and optional32-byte digest; outpoint digest32 bytes followed by index4 bytes. |
| `Bitcoin.buildTapleafSimplicity` | `TapLeaf`, not `TapLeaf/elements`; version0xbe, CMR length32, the literal full shift/padding tree and784-bit length. |
| `Bitcoin.buildTapbranch` | `TapBranch`, ordering by the canonical256-bit less-than term, then the second compression with2^511+1024 padding. |

The compression's `add32` and finalizer's64-bit addition use `Word.adder`
at depths5 and6. At every positive depth its definition is exactly the
canonical `false &&& iden >>> fullAdder`; no bit-base structural identity is
assumed. The recursive full adder and bitwise/shift/rotate, subtraction,
padding and buffer dependencies are included in the selected source model.
Haskell `Word`, `Vector` and `Buffer` carriers/conversions are pinned through
the complete type module. This is source correspondence, not verification of
GHC, native integer or lens libraries.

The tag constants are not justified just by comments or by a native hash
calculation: the kernel-checked imported Coq results relate each padded ASCII
tag block to its tag digest through the original `hashBlock`, then compress
two copies to obtain the prefix. Their exact statements are source-guarded.
The corresponding Haskell `tagIv`, `ivHash`, `bslHash` and `bsHash` expressions
are pinned, while equivalence of their external crypto/bytestring libraries
remains an explicit unproved boundary.

The startup state pins portable C compression dispatch, the actual global
maximum counter, tag bytes and physical permission/extent conditions. The
formal contracts include whole `Clight2.eval_funcall`, success/failure result,
output cells, cursor, prefix/load preservation and re-established startup
state. Actual initial-memory nonvacuity is proved, not presumed by this tool.
The17 explicit `memcpy_model` premises and eight inherited endpoint
assumptions are unchanged. Optimized dispatch and assertion-enabled build
support are not added by this review.

## Reproduction and evidence

The fixed model was first captured with `create-model.py` (which refuses to
overwrite it), then extended additively after reviewing transitive word,
bit, order, padding and type dependencies. No old comparison was replaced
or weakened and no C/Haskell/Coq input was changed to pass this gate. The
committed model is authoritative; do not regenerate it from changed sources.

`check-source.py` performs the actual read-only comparison. `test-source.py`
mutates its in-memory view only: it never edits a source tree or compiles a
corrupted theorem. The initial298-fixture suite passed. The extended suite
needed one test-harness correction to handle an exact import-line pattern
without a capture group; this was an `IndexError`, not a C/Coq discrepancy.
The extended327-fixture suite and the once-only source controller both
completed with exit zero under handle78280. `SOURCE-REVIEW.json` and exact
positive/negative logs bind the terminal result. The completed command was:

```sh
python3 -B proof-work/sha-canonical-startup-source/finish-source.py /private/tmp/jet-sha-canonical-startup.8SBgLe7u
```

It requires the actual successful kernel/AST launch, receipts, exact sources,
fresh objects and logs before running positive/negative source checks, and
checks that main inputs, the staged patch and the private source fingerprint
are unchanged afterwards. Independent full evidence review, normal
registration/admission and the all-jet goal still remain.
