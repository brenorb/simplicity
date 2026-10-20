# Original scalar reader: complete function lifecycle

The nine results in `jet_secp_scalar_reader_lifecycle.v.source` complete the
original `f_read_scalar` helper around the already checked 31-result body
archive in `../scalar-reader`. No C AST, executor or production source changes.

`eval_scalar_reader_numeric_owned` derives actual Clight function execution,
four actual reduced Mint64 limb loads, their big-endian input value modulo the
canonical group order, source cursor advance by 256, final 32/16-byte caller
region ownership, the read invariant and outside-footprint framing.
It uses actual `fn_vars` allocation, actual entry/bind, both original C calls
(including the NULL overflow pointer), actual void return and `Mem.free_list`
of the local 32-byte buffer. None of these is an assumed execution premise.

This is an **internal reader helper**, not public scalar-zero jet equivalence.
The caller must establish its two owned zero-base scalar/source blocks, frame
input/output predicates, separation and initial invariant. Input length is
256; the nonnegative cursor plus 256 must fit uint64. The execution uses the
existing LP64 RECKLESS assertion-disabled AST and inherited frame contracts.
No canonical-input restriction is added: scalar reduction covers arbitrary
256-bit input, including the group order. Registered checkout coverage stays
351/533; public coverage added by this archive is zero.

## Next boundary

Use the reduced-limb representation to invoke the already checked actual
scalar-is-zero helper, then prove the public jet's real 16+32-byte allocation,
source-frame copy, read/helper/writeBit calls, true return and both local frees.
The public specification must remain the literal canonical term testing raw
zero OR raw group order, not a numeric replacement. Fresh source/parametricity
gates and full acceptance remain required before registration.

Do not retry whole-reader `xfun`: the diagnosed int-to-NULL cast limitation is
already handled by the checked actual-call adapter. SHA startup and memcpy
remain reserved for Claude. All work and signed commits remain local.
