# Unprototyped concept: whole P-256 ECDSA verification

The corpus implements [bounded P-256 verification](../../src/JetDiscovery/Corpus/P256.hs)
and a [WebAuthn withdrawal](../../reports/CRYPTO-FAMILIES.md). Both perform
the actual curve check with a witness-supplied inverse that the program
verifies. A whole verification jet would need a separate, agreed interface
for public-key encoding, digest, signature, canonical range and failure
behavior. This concept has no registered reference arrow or isolated
occurrence, price, or saving in the executable overlay.

Use the [per-program costs](../../reports/corpus-results.md) and the
[prototype for field multiplication](../p256_fe_multiply/README.md) to
compare existing jets with a measured field-only overlay. Passkeys and
external P-256 signatures are practical workloads. Existing secp256k1
field/group proofs suggest a structure for the C and Coq work, but the
new prime, scalar arithmetic, point operations, signature semantics and
implementation need independent proofs and benchmarks. A curve-level
linear verification primitive is another plausible API to compare.
