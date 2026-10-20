# Three hash getters: forced current-source rebuild

This new run covers the original C outputsHash, inputUTXOsHash and
issuanceBlindingEntropyHash getter candidates. The literal `one word8`
blinding endpoint is the canonical one; the intermediate constant-scribe
adapter is support, not another jet.

These contracts retain explicit initial caller-cache relations. They do not
establish the cached hashes from the real environment builders. They add zero
normal registered coverage, and do not pass or relax the separate failing
original Bitcoin primitive-identity gate. C, original specifications, API and
generation settings remain fixed.
