# Three hash getters: forced current-source rebuild

This new run covers the original C outputsHash, inputUTXOsHash and
issuanceBlindingEntropyHash getter candidates. The literal `one word8`
blinding endpoint is the canonical one; the intermediate constant-scribe
adapter is support, not another jet.

The full forced build completed successfully: 28 results, 21 definitions,
18 closed results, six results using only functional extensionality and four
endpoint declarations using the six inherited execution dependencies. There
are three distinct target jets. `RUN.json` records the exact inputs and
complete reports. The earlier inventory-name failure is preserved separately
in `first-attempt/`, including the original driver and terminal classification.

`SOURCE-CLOSURE.json` binds every loaded local source and object to the
successful `make -B` trace: 315 project modules, including the restored original
Bitcoin module. It does not reuse the older stale Bitcoin object.
`SOURCE-CHECKED.json` records successful recursive kernel checking, with
that complete local closure unchanged before and after the check. The source-bound
driver completed with exit 0. Pinned external Coq/CompCert/VST libraries
are a separate trust boundary, not rebuilt by this local command.

These contracts retain explicit initial caller-cache relations. They do not
establish the cached hashes from the real environment builders. They add zero
normal registered coverage, and do not pass or relax the separate failing
original Bitcoin primitive-identity gate. C, original specifications, API and
generation settings remain fixed.
