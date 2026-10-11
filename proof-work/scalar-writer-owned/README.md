# Actual scalar serializer with retained ownership

Six compiled and independently kernel-checked internal results execute the
unchanged `f_secp256k1_scalar_get_b32` on the actual two 32-byte owned regions.
The original helper's output is exactly its previously checked big-endian
byte representation. Both buffer and scalar retain Freeable permissions.
No desired execution/output/free fact is assumed, and no memcpy premise or
production C change is involved.

The numeric helper starts from the explicit serializer input representation
and a 256-bit value bound, produces the actual Clight call and uint8 array,
and retains representation, both bases/Freeable ranges and the external memory
frame. Those input storage facts must still be derived by the enclosing caller
from actual reader output and a fresh buffer allocation. This is **not** a
complete `write_scalar` lifecycle or public `scalar_normalize` equivalence.

Independent kernel session 1857 exited 0. Six types and three non-tree
definitions were read untruncated; each exact dependency set was inspected.
Three results are closed, one depends on four inherited classical/extensionality
axioms and two additionally use CompCert's execution-semantic parameters.
The imported kernel context has 15 inherited axioms and all unsafe categories
empty. The computed executor tree is diagnostic; formal run/shape equalities
and actual original-function execution are the proofs, not printed tree text.

Pinned Coq 8.17.1/CompCert 3.14/VST 2.14, stack 65520 KiB, cwd
`/tmp/jet-ge-negate-accept.5mtyZa/Coq`; two narrow load paths:
`-R /tmp/jet-scalar-reverify.8hswEF OriginalC` and
`-R /tmp/jet-scalar-writer.khT8eN WriterC`. The manifest records exact hashes,
terminal receipts and the full kernel command. Sources are `.source` archives,
outside accepted load paths. This adds zero public coverage.

```sh
python3 proof-work/scalar-writer-owned/review.py --work /tmp/jet-scalar-writer.khT8eN
python3 proof-work/scalar-writer-owned/test-review.py /tmp/jet-scalar-writer.khT8eN
```

Next: establish exact reader-to-serializer limb correspondence; derive owned
initial regions from ordinary storage; compose original `write_scalar`'s
get_b32/write8s calls and actual entry/allocation/return/buffer-free; then
compose public scalar_normalize against the literal canonical term. Do not
edit the frozen scalar-zero acceptance candidate. Shared core frame
constructibility, memcpy linkage and SHA startup remain Claude's reservation.
