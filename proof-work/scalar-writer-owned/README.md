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

Next: establish exact reader-to-serializer limb correspondence; derive owned
initial regions from ordinary storage; compose original `write_scalar`'s
get_b32/write8s calls and actual entry/allocation/return/buffer-free; then
compose public scalar_normalize against the literal canonical term. Do not
edit the frozen scalar-zero acceptance candidate. Shared core frame
constructibility, memcpy linkage and SHA startup remain Claude's reservation.
