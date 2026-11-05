# Unprototyped concept: monolithic SHRINCS verification

The corpus contains separate full [stateful](../../src/JetDiscovery/Corpus/Shrincs.hs)
and [stateless](../../src/JetDiscovery/Corpus/ShrincsStateless.hs) SHRINCS
profiles and a separate [FIPS 205 baseline](../../reports/SLH-DSA-BASELINE.md).
The stateless profiles share FORS and hypertree structure, with their own
parameter and encoding rules. The study does not define a common full
verification arrow or give the monolithic idea a measured cost, exact
match count, or recommendation score.

Use the [whole program rows](../../reports/corpus-results.md) and the
[tweaked SHA-256 chain prototypes](../sha256_wots_chain_16/README.md) to
see the actual measurements and the narrower candidate estimates.
A monolithic verifier would need to bind the precise formats, both
branches, the WOTS+C constant sum, FXMSS, FORS and hypertree policy.
Reusable SHA-256 compression proofs support those implementations.
The full encoding, checked domain separation and integration proof
would remain new work. A chain or tweakable-hash primitive offers a
smaller independently testable change.
