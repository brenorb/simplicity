# Four-local calculation frame entry

Six closed preparation lemmas compile and pass recursive kernel checking:
the three actual jet headers, the actual frame/midstate sizes, and one shared
`function_entry2` derivation for src/entropy/result/`__res` allocations of
16/32/32/32 bytes. The final lemma handles the concrete original Elements
global environment. It does not assume an entire jet call or final output.
Its allocation equalities are intermediate entry premises; the enclosing public
proof still must derive the four allocations itself.

This is **not** complete equivalence for the three public frame jets and adds
zero accepted coverage. Compose the actual body next: source-frame copy,
read32s of eight entropy words, canonical helper call into `__res`, struct copy
to result, writeHash, true return, and freeing all four locals. The canonical
helper contracts are in `../elements-calculation-calls/`; their libc and
dispatch premises remain explicit. Prove source/output cursor, prefix and
outside-load framing from initial frames, not extra post-read/output premises.
The public jets use cc_default; the hidden struct-return helper calls use
cc_structret=true. Do not conflate the two interfaces.
