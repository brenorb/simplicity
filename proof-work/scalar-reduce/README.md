# Scalar reduction value bridge

This is an internal continuation of `../scalar-next`, preserving its
`OriginalC` namespace and all 23 reviewed helper sources unchanged. It adds
one freshly compiled module with 20 completed results and 17 definitions.
No public jet coverage or full acceptance is claimed.

The final checked declaration is `eval_scalar_reduce_numeric`. From the
existing writable four-limb representation and the internally supplied
overflow flag, it proves the actual original Clight scalar_reduce call,
return flag, four current-memory loads, output value modulo the group order,
post-call representation and outside-footprint framing. The reader must
derive the flag from the actual overflow call; this is not a permissible
additional precondition on a public scalar jet.

The arithmetic decomposition is reusable: three arbitrary uint64 additions
and their two carry bits give exact quotient/remainder without restricting
overflow; the reduction's exact executor output is matched to those steps.
A weighted carry telescope accounts for the final 256-bit wrap. The bounded
canonical input and its derived comparison flag then identify that wrap with
reduction modulo the group order. Closed constants are normalized separately;
no symbolic-memory `vm_compute`, admissions, or new assumed declarations.

Verification on Coq 8.17.1 / CompCert 3.14 / VST 2.14:

The next milestone is now compiled in `../scalar-set`: actual scalar_set_b32
byte assembly, derived overflow flag, reduced output loads and the owned NULL
call preserving both allocated regions' Freeable permissions. Its independent
kernel audit is tracked there; this archive's 20-result inputs are unchanged.
Next: establish that owned input contract from the real allocated/read8s buffer,
then read_scalar's allocation/read8s/NULL-set/free, the public scalar_is_zero
lifecycle and literal canonical specification/source gates. SHA and memcpy
remain reserved for the coordinated separate session.
