# Calculation helpers in the original Elements program

This is an isolated proof-support port, not a change to C or generation
settings and not yet complete public-jet equivalence. The private tree is
`/private/tmp/jet-elements-calculation-calls.zahGaG`.

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

The first forced build (94519) terminated with exit 1 at the extracted
field lemma's missing `MID` notation. Its original driver/source/logs are
preserved in `first-attempt/`. Only after all make children finished was the
missing proof-support import added. The full forced retry **99090 passed**.
`RUN.json` records all 55 results and 20 definitions: 38 closed, ten with the
four inherited expression dependencies and seven with the six inherited
execution dependencies. The exact per-result inventory is independently
reviewed by `calls.py`. `SOURCE-CLOSURE.json` binds all **196** loaded local
sources/objects to that successful forced build, including the explicit AST
proof-loading alias. Compilation is not recursive acceptance or a public jet
lifecycle.

The helper-call extension is external to this frozen tree at
`/private/tmp/jet-elements-calculation-word.6TxiYD/CalculationCalls.v`.
It **compiled successfully**, with complete reports for seven results and
three definitions in `CALLS-RUN.json`. The actual `elements_ge` asset/explicit-
token/confidential-token helper calls return the canonical word-program values
and preserve the stated memory framing/permissions. Libc/dispatch premises
remain explicit; no desired cache/hash or execution is assumed. The three
dispatch/array lemmas have the four inherited CompCert dependencies, and the
four concrete/generic execution results retain exactly the six inherited ones.

The initial strict metadata check wrongly expected the three memory/dispatch
lemmas to be closed. It refused the run; the exact driver/reports and terminal
result are preserved in `first-calls-attempt/`. After inspecting the full
reports, only that classification was corrected and the full extension compile/
reports rerun; no Coq proof or target changed. The source-bound recursive check
is **76211**, covering the extension and all 196 base modules. Poll that handle
and preserve its terminal result. Only successful `CALLS-CHECKED.json` proves
that recursive checking passed. Do not edit its sources, base objects or drivers
while live, or count the helper results as three complete public jets.

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
