# Four-local calculation frame entry

Six closed preparation lemmas compile and pass recursive kernel checking:
the three actual jet headers, the actual frame/midstate sizes, and one shared
`function_entry2` derivation for src/entropy/result/`__res` allocations of
16/32/32/32 bytes. The final lemma handles the concrete original Elements
global environment. It does not assume an entire jet call or final output.
Its allocation equalities are intermediate entry premises; the enclosing public
proof still must derive the four allocations itself.

`RUN.json` and `CHECKED.json` bind the exact extension source/object, complete
six-result/five-definition reports and the source-bound original-program
dependencies from `../elements-issuance-computed/`. Every theorem has an empty
assumption set. This small prefix loads a subset of the existing approved
library axiom context, recorded exactly in `CHECKED.json`; no normal gate or
allowlist was modified. Unsafe-kernel and positivity flags remain absent.

The current external source is
`/private/tmp/jet-elements-calculation-frame.b2dBAy/CalculationFrame.v`.
`verify.py EXTERNAL_DIRECTORY` performs the once-only compile/report/source-
binding/kernel audit. Existing receipts must not be overwritten.

This is **not** complete equivalence for the three public frame jets and adds
zero accepted coverage. Compose the actual body next: source-frame copy,
read32s of eight entropy words, canonical helper call into `__res`, struct copy
to result, writeHash, true return, and freeing all four locals. The canonical
helper contracts are in `../elements-calculation-calls/`; their libc and
dispatch premises remain explicit. Prove source/output cursor, prefix and
outside-load framing from initial frames, not extra post-read/output premises.
The public jets use cc_default; the hidden struct-return helper calls use
cc_structret=true. Do not conflate the two interfaces.
