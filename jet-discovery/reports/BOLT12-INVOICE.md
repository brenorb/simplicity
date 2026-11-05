# Complete bounded BOLT12 invoice client reader

`app-bolt12-invoice-authorization` verifies a complete supported raw invoice profile, its copied request, actual signature and payment-acceptance conditions. It is explicitly a client verifier. The client supplies its authenticated stored request, reply-path context and current UTC time; transaction nLockTime is not used as evidence of present time. No payment, route execution or paid receipt is claimed. Hash/Merkle/signature helpers do not create extra application groups.

The primary [BOLT12](https://github.com/lightning/bolts/blob/191462825ae341f0a27098765c075f01ca9bc6c2/12-offer-encoding.md) and [BOLT4](https://github.com/lightning/bolts/blob/191462825ae341f0a27098765c075f01ca9bc6c2/04-onion-routing.md) definitions are by the BOLTs contributors, pinned at `191462825ae341f0a27098765c075f01ca9bc6c2`, CC-BY4.0. The full inert repository archive and all official BOLT12 JSON packets are retained with URL/revision/license/hash metadata. GitHub's tree API returned403 rate-limit; a successful immutable codeload archive supplied complete source/vector discovery. Nothing downloaded is executed.

The structured proof contains the actual raw<=511-byte TLV stream, seven decoded dynamic fields and a BIP340 signature. After hashing the raw stream once, the program reconstructs every supported canonical TLV byte and requires its hash to match. Thus sorted type order, BigSize lengths, required field presence, exact signature bytes and the profile's copied/unknown fields are bound to the actual input. It rejects unsupported fields or encodings; it never silently removes them. One structured `witness` binds all logical input values; every later use is a projection.

The remembered request commits metadata, offer description, merchant issuer identity,1000-msat request amount, payer key and an unknown odd type99. The invoice must copy those fields exactly. It includes one known one-hop blinded path, exactly one payinfo with empty allowed-feature bits, creation timestamp, explicit expiry, payment hash, amount, one-byte invoice features, merchant node identity and the signature. An unknown high invoice type3000000001 is included in the transcript. These fixed values define the bounded profile; they are not hints supplied by an adversarial proof.

The program computes every `LnLeaf`, the exact binary `LnNonce||firstTLV` tag and the sorted `LnBranch` uneven tree. It excludes only signature-range fields and verifies the merchant's actual `lightninginvoicesignature` BIP340 signature. All copied and unknown non-signature fields affect that root. For this request-committed profile the constant nonce hashes are precomputed from fixed tag/type bytes; every dynamic leaf and branch still runs in Simplicity.

The acceptance policy requires the requested1000 msat, nonzero hop count, a matching usable path amount range, minimal timestamp/expiry/feature encodings and no unknown even invoice feature bit. Unknown odd feature bits are ignored. It checks actual client UTC against creation plus expiry, accepts the exact expiration boundary and applies an explicitly stronger no-future-creation client policy. The timestamp/expiry bound is minimal4/2-byte truncated integers; other widths and optional-field profiles are outside this predicate. It permits single-part payment only.

The route's public points and opaque encrypted-hop bytes come from the official payer-proof invoice fixture. Invoice readers cannot decrypt those final-hop bytes. This implementation checks the complete reader/authorization statement under its committed route profile; it does not prove route viability, channel liquidity, receiver decryption, networking or payment success. The published invoice examples are test transcripts, not evidence of a live route; their original tiny4/5-msat payinfo limits do not meet this application's1000-msat authorization policy. Complete accepted examples therefore use clearly derived and newly signed full invoice profiles with a suitable maximum. Test metadata/public private keys are fixtures, not production entropy.

| Complete raw-invoice vector | Expected / actual |
| --- | --- |
| Authentic invoice with copied unknown odd field and high unknown invoice field | Accept / Accept |
| Client UTC equals exact expiration boundary | Accept / Accept |
| Fresh merchant signature changes requested amount | Reject / Reject |
| Fresh merchant signature on expired invoice | Reject / Reject |
| Future creation time violates stated client policy | Reject / Reject |
| Fresh signature on unknown even feature | Reject / Reject |
| Fresh signature on nonminimal zero feature byte | Reject / Reject |
| Fresh signature on zero-hop path | Reject / Reject |
| Fresh signature with no usable path amount range | Reject / Reject |
| Fresh signature on nonminimal expiry width | Reject / Reject |
| Fresh signature changes copied unknown request field | Reject / Reject |
| Fresh signature omits mandatory payment_hash | Reject / Reject |
| Fresh signature duplicates a known TLV | Reject / Reject |
| Actual raw invoice encodes an invalid signature | Reject / Reject |

All14 actual jetted Haskell Simplicity cases pass with canonical per-vector whole-program CMR `f3f640931d1dfa224b50b948521a0bb7d8b5bef5fb2e9f168c480da73c9f7e39`. GHC9.8.4 `-O1`, `-N1 -M3G -s`:79.187 seconds elapsed, max live1,161,858,904 bytes and total RTS memory2356MiB. Exact source/runner snapshots, driver/data hashes, executable/log hashes and results are in `data/bolt12-invoice-provenance.json`. This is not a full-corpus cost or onchain spending result.

All97 official BOLT12 JSON rows are inventoried. The independent byte/Integer reference checks all4 published Merkle/signature-tree cores and all5 published complete raw invoice signatures embedded in the payer-proof valid set. The remaining offer/string/payer-proof tests are outside this complete invoice-reader profile; they are not represented as covered native transactions. The reference additionally parses and validates the actual complete derived raw invoice and freshly signed amount/expiry/feature/path negatives. `bolt12-derived-invoice.hex`/`.tsv` retain that fixture, with explicit client time.

Sources are `Lib.Bolt12Invoice` and `Ref.Bolt12Invoice`; reproducible tools are `extract_bolt12_invoice_vectors.py`, `Bolt12InvoiceReference.hs` and `Bolt12InvoiceSmoke.hs`. ASCII bech32-style transport decoding, remembered request/reply authentication, UTC acquisition and routing remain client boundaries. The harness's native transaction environment is unused, so budget comparisons do not imply enforceability as a Bitcoin spend.
