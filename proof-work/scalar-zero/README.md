# Complete scalar-zero implementation-to-literal local contract

`scalar_zero_local_spec` proves the original public
`f_simplicity_scalar_is_zero` against `canonical_scalar_is_zero`, the literal
Simplicity program port. Its input domain is **all Word256 values**, including
the raw secp256k1 group order; it is not restricted to normalized scalars.
The port checks the canonical program's disjunction of raw zero and equality
to the group order. Numeric reduction facts are internal bridges, not a
replacement public specification.

The proof derives original function entry, 16-byte source-frame and 32-byte
scalar allocation, actual by-value source copy, the complete original scalar
reader (including its 32-byte buffer allocation/release), original reduction
and zero test, writeBit, true return, and actual release of both public locals.
It proves encoded output, cursor updates and the inherited local memory frame.
There is no memcpy-model premise and no assumed public call/output/free fact.
Internal call adapters take helper executions; the complete caller discharges
them from the checked implementations.

This is **not yet full acceptance or checkout registration**. The public
theorem inherits `secp_jet_local_spec`'s LP64, assertion-disabled RECKLESS
configuration and local frame premises. It does not establish arbitrary
evaluator frame constructibility, assertion-enabled execution, whole evaluator
integration, or a new C/specification configuration. Registered main-checkout
coverage remains 351/533; this archive adds zero. The accepted affine isolated
candidate has 355/533 and is a separate baseline, not checkout integration.

Next: assemble a fresh isolated candidate over the immutable accepted affine
baseline, transport these modules to namespace C with fresh compilation,
review all added types/definitions/dependencies and literal-source gates, then
run normal full acceptance before registry integration. Preserve the checkout's
unrelated staged/dirty SHA and coverage work. Claude reserves shared memcpy
linkage, SHA startup and general core frame constructibility; our caller-specific
scalar lifecycle does not overlap those reservations. No remote pushes.
