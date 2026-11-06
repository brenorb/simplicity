# Candidate: `sha512_compress` — SHA-512 compression function

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Strong**: The estimate brings the native BIP32 withdrawal below its fixed-stack scenario. The same compression is useful in HMAC, Ed25519 and BIP47 client work, which is reported separately. Benchmark the reusable block primitive.

Price: **1.147 WU (ESTIMATE)**. 1.5 x Sha256Block: SHA-512 compresses 128 bytes with 64-bit words (as blake2b_compress)

Matches in 4 of 157 registered rows: 4 matched DAG nodes across all branches, 18 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| xchain-sha512 | kernel | 1 | 1 | 5,454.166 | 17.797 | 5,436.369 | no / yes at 3990 WU |
| xchain-ed25519 | native_full_verifier | 1 | 1 | 2,925,636.828 | 2,920,200.459 | 5,436.369 | no / no at 18820 WU |
| app-bip47-notification-payment-client | client | 12 | 1 | 69,731.129 | 4,494.701 | 65,236.428 | n/a (client) |
| app-bip32-public-hd-withdrawal | native_full_spend | 4 | 1 | 22,481.299 | 735.823 | 21,745.476 | no / yes at 5611 WU |

See the [complete matrix](../../reports/candidate-ranking.md#sha512_compress) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`(Vector8 Word64, Vector16 Word64) -> Vector8 Word64`

## Specification
`JetDiscovery.Corpus.Ed25519.sha512Compress` (FIPS 180-4); reproduces the FIPS 180-4 digest of "abc" and the
SHA-512 values inside the RFC 8032 ed25519 test vectors.

## Cost (ESTIMATE)
ESTIMATE: 1.5 x `Sha256Block` = 1.147 WU (80 rounds on 64-bit words over a 128-byte block, as `blake2b_compress`).

## Generality
Ed25519 (RFC 8032) challenge hashes, BIP 32 / SLIP-10 HMAC-SHA512 key derivation, Solana and Cardano signatures.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium: the SHA-256 compression proof structure carries over with 64-bit words.

## Alternatives considered
None smaller: the whole ed25519 verification jet would include it.

## Reference checks

The standalone probe matches all nine direct compressor calls against `JetDiscovery.Ref.HmacSha512.sha512`. It starts from the standard IV and passes one padded block for each message, including the empty message and the 111-byte single-block limit. [Probe](../../tools/HashCompressionReferenceProbe.hs) · [Results](../../reports/data/hash-compression-reference-probe.txt) · [Provenance](../../reports/data/hash-compression-reference-provenance.json)
