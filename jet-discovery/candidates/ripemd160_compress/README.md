# Candidate: `ripemd160_compress` — RIPEMD-160 compression function

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: Several Bitcoin HASH160 and interoperability paths match the same compression. Verify whether a compression jet changes spend fit often enough to justify the new dual-lane proof alongside the broader SHA candidates.

Price: **0.765 WU (ESTIMATE)**. Sha256Block: RIPEMD-160 and SHA-256 compression cost about the same in software

Matches in 5 of 157 registered rows: 5 matched DAG nodes across all branches, 5 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| xchain-ripemd160 | kernel | 1 | 1 | 2,469.559 | 14.139 | 2,455.420 | yes / yes at 5230 WU |
| app-htlc-hash160 | native_full_spend | 1 | 1 | 2,546.490 | 91.070 | 2,455.420 | yes / yes at 5463 WU |
| app-silent-payment-output-covenant | native_full_spend | 1 | 1 | 4,296.691 | 1,841.271 | 2,455.420 | yes / yes at 7494 WU |
| app-ark-round-refresh | client | 1 | 1 | 5,897.705 | 3,442.285 | 2,455.420 | n/a (client) |
| app-bip47-notification-payment-client | client | 1 | 1 | 69,731.129 | 67,275.709 | 2,455.420 | n/a (client) |

See the [complete matrix](../../reports/candidate-ranking.md#ripemd160_compress) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`((Word32, Word32, Word32, Word32, Word32), Vector16 Word32) -> (Word32, Word32, Word32, Word32, Word32)`
(state and message words little-endian, as in the RIPEMD-160 specification)

## Specification
`JetDiscovery.Lib.Ripemd160.ripemd160Compress`; reproduces the published RIPEMD-160 digests of "" and "abc"
(`xchain-ripemd160`, `cabal test`).

## Cost (ESTIMATE)
ESTIMATE: `Sha256Block` = 0.765 WU (RIPEMD-160's 160 steps on 32-bit words cost about one SHA-256 compression in
software).

## Generality
Bitcoin-native: HASH160 (`RIPEMD160(SHA256(x))`) is Script's key hash (P2PKH, P2WPKH) and the BOLT 3 HTLC payment
hash. Script-compatible HTLCs, PTLC fallbacks and key-hash commitments need it. Also Ethereum's ripemd160
precompile.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium, like SHA-256 compression: a fixed sequence of 32-bit operations with two parallel lines. The C code is in
Bitcoin Core (`crypto/ripemd160.cpp`), not libsecp256k1.

## Alternatives considered
A whole `hash160_32` jet (SHA-256 then RIPEMD-160 of a 32-byte value) covers the HTLC and key-hash uses in one call.

## Reference checks

The standalone probe matches all ten direct compressor calls against `JetDiscovery.Corpus.Ripemd.ripemd160Ref`. It starts from the standard IV and passes one padded block for each message, including the empty message and the 55-byte single-block limit. [Probe](../../tools/HashCompressionReferenceProbe.hs) · [Results](../../reports/data/hash-compression-reference-probe.txt) · [Provenance](../../reports/data/hash-compression-reference-provenance.json)
