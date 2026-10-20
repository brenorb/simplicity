# Calculation helpers in the original Elements program

In that tree only, `Coq/C/jets_sha.v` is a byte-identical proof-loading copy
of the original `Coq/C/jets_elements.v`. The existing closed
`elements_sha_program` and `elements_sha_genv` proofs are verification roots.
The actual target program and its helper bodies must be equal; no result for
the environment translation unit is imported as an execution theorem for the
original jet. The main SHA module and all production targets remain unchanged.

The two existing calc/calc_token execution proofs are retained, with their
statements, proof bodies, explicit `memcpy_model` and dispatch premises. Only
imports are narrowed: generic field evaluation and its midstate-array lemma
are extracted; unrelated raw-environment field/isFee facts are not imported.
The Boolean `b2i` definition is copied exactly, and the midstate-array lemma
is renamed. `check-port.py` validates these precise transformations against
the existing sources and rejects eight in-memory mutations. This source guard
does not replace compilation, assumption review or kernel checking.

The original enclosing asset/explicit-token/confidential-token jets have four
locals: src (16 bytes), entropy (32), result (32), and the normalized struct
return slot `__res` (32). All three have no temporaries. Their common body is
source copy; read32s of eight entropy words; helper call into `__res`; struct
copy into result; writeHash; true return. The helper call convention has
`cc_structret = true`, unlike the ordinary void pointer-helper templates.
Do not accidentally use a cc_default call rule. The existing
`hash256_reg_chunks` bridge connects the reader's words to the canonical input.
Allocation, these calls, cursor/output/prefix/load framing and freeing all four
locals still need composition for the actual public frame-jet theorem.
