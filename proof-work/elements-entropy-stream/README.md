# Original C entropy helper to canonical Simplicity

`elements_entropy_helper_word_call` proves the actual
`simplicity_generateIssuanceEntropy` call in the original `elements_ge` returns
the canonical `calculate_issuance_entropy_spec` registers. It derives the output
and memory framing from initial txid/index/contract representation and writable
result space. The libc model and actual dispatch/maximum-counter state remain
explicit. It assumes neither a desired output nor execution of the helper.

`Short` bridges both C streaming SHA phases to the word program, including the
four little-endian index bytes, lengths 36/32, padding, double-hash and final
contract compression. `ByteBlocks` extracts the generic block-algebra prefix
of the existing bytestring proof; no environment-only `hashBuffer` execution
is imported. `Registers` is an unchanged, freshly compiled copy of the four
canonical entropy register lemmas.

The first inventory check found that the canonical specification module also
needed fresh-source provenance, in addition to its register module. It refused
to issue a receipt; its exact driver/reports are preserved in `first-attempt/`.
The retry explicitly compiles and reports both dependencies. No Coq proof or
target was changed to satisfy that check.

This is not yet the enclosing `simplicity_calculate_issuance_entropy` frame
jet: its 544-bit reader prefix, five locals, struct copy, writer and return/free
must still be composed from initial public frames. The three completed
calculation jets provide that pattern. No C, original specification, API,
generation setting, normal registry or accepted-coverage count is changed.

The input width is 256 + 32 + 256 = 544 bits. The C index field/carrier is
64-bit, but `simplicity_read32` consumes 32 input bits; its carrier width must
not be added to the logical frame size. The formal helper contract already
uses Word32; the earlier 576-bit continuation note was a documentation error.
