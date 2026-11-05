# Cost-only concept: BIP 341 precomputed transaction hashes

The study prices a stand-in for this family. It has no executable candidate
arrow, exact DAG occurrence count, or recommendation score. The measured
template programs and separate stand-in bounds are in
[what-if analysis](../../reports/whatif.md).

The proposed accessors would return BIP 341's SHA-256 hashes of serialized
outputs, sequences, previous outpoints, amounts, scriptPubKeys and the
current annex. A separate BIP 119 accessor would return the optional
scriptSig hash. The transaction environment exposes several native hashes
but lacks raw script bytes for the byte-compatible calculations. The
stand-in treats the transaction-wide work as precomputed and prices
access like the existing transaction-hash jets. This is an **ESTIMATE**.
Its C implementation, caching effects and cost are unmeasured.

The byte-exact BIP 119 and BIP 446 corpus programs reconstruct serialization
from checked raw-script witnesses. They have independently inventoried
upstream vectors; their verdicts and exact scope are in
[the BIP table](../../reports/bip-verdicts.md). The native CTV variant
commits to the same transaction fields using the existing native hashes,
with a different wire digest. When exact BIP wire compatibility matters,
a transaction-environment accessor would also require a C/Haskell
serialization equivalence proof. A native output covenant can use
the existing hashes where compatibility is unnecessary.
