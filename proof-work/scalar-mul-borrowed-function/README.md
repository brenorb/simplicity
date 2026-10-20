# Borrowed-rhs scalar multiplication: complete internal function

The actual `f_secp256k1_scalar_mul` call for `r=a`, with a writable owned
32-byte input/output and a non-owned readable rhs, now includes real function
entry, a fresh uninitialized 64-byte product allocation, the checked multiply
and reduction calls, and real local-buffer free. Four output loads after free
are observed; their exact value is the product modulo the canonical group order.
The rhs remains readable and represented. No writability or ownership is
required for it.

This is **not** a public `scalar_multiply_lambda` equivalence theorem, a
normal-namespace integration, or new coverage. Public lambda still needs its
literal specification, the actual readonly global's initial/preserved
representation, reader/writer/cursor framing and the original jet's cleanup.

## Continue

First establish the four actual `secp256k1_const_lambda` limbs from the
generated original global and `Genv.init_mem`, with readonly permission only.
Reuse that relation through allocation and through the real caller's frame.
Port the pinned `scalar_lambda = scribe256 lambda` and
`(unit >>> scalar_lambda) &&& iden >>> scalar_multiply` literally; discharge
the C-versus-spec operand order with a formal value bridge. Compose the
complete borrowed helper with the existing original reader, serializer and
private-local cleanup. Do not turn initialization, helper execution, output
or free into a new public precondition.
