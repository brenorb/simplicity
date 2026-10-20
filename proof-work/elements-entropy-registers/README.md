# Entropy calculation register bridge

Four closed lemmas expose the original canonical calculation program as the
register formulas needed by the C entropy-helper proof. The first outpoint
compression includes the byte-swapped index, `0x80000000` padding, five zero
words and bit length 288. The second includes the first hash, the padding word,
six zero words and bit length 256. The final entropy compression appends the
contract hash to the double-hashed outpoint.

These are intermediate representation bridges, not a replacement mathematical
specification and not a C execution or full jet theorem. The bridge still has
to meet the C streaming-byte/padding result `entropy_regs`; the enclosing jet's
frame lifecycle remains to be derived.

The full compile/reports passed: all four results are closed. The first driver
attempt retained the old load-path namespace and failed while importing the
assumption report; its driver/logs are preserved in `first-attempt/`. Only the
load-path name was corrected before the full successful retry, without a Coq
proof change. Recursive kernel checking remains separate.
