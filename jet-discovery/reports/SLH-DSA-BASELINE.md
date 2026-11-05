# Standard FIPS 205 baseline

The new `pq-slh-dsa-sha2-128s` row implements the standard pure
SLH-DSA-SHA2-128s verification relation. The earlier SHRINCS stateless row uses
that construction with different parameters and a SHRINCS-specific message;
it is not a standard FIPS 205 parameter set. This required baseline receives
no extra distinct-program credit merely for changing hash-family parameters.

| Field | Existing SHRINCS stateless path | Standard baseline |
| --- | --- | --- |
| Specification | Pinned SHRINCS draft | FIPS 205, published 2024-08-13 |
| n / h / d / h' / k / a | 16 / 45 / 5 / 9 / 10 / 13 | 16 / 63 / 7 / 9 / 14 / 12 |
| Public-key bytes | 48, including the stateful root | 32: PK.seed then PK.root |
| Signature bytes | 5776 | 7856 |
| FORS proof fields | 10 × (1 + 13) | 14 × (1 + 12) |
| Hypertree proof fields | 5 × (35 chains + 9 siblings) | 7 × (35 chains + 9 siblings) |
| Bound message in this transaction profile | Empty context, stateful root and sig_all_hash | Pure external interface, empty context and sig_all_hash |
| WOTS kernel | Shared fixed-block n16 frontend | Same primitive, 245 source-level calls |
| Distinct counting credit | Existing group | Same hash-family parameter group; no extra group |
| Current WU / isolated candidate impact | Full rerun required | Pending full runner measurement |

The reference is [Ref.SlhDsaStandard](../src/JetDiscovery/Ref/SlhDsaStandard.hs),
and the Simplicity implementation is
[Corpus.SlhDsaStandard](../src/JetDiscovery/Corpus/SlhDsaStandard.hs). It implements
FORS, WOTS checksum/chains, public-key compression and all seven authentication
layers. Compressed addresses have the exact 1+8+1+4+4+4 byte layout. H_msg uses
MGF1-SHA-256, a 30-byte output split into 21 digest bytes, 54 tree bits and
9 leaf bits. The external pure profile frames its message as
`0x00 || context_length || context || message`.

The public-key/randomizer header enters once; each of the 490 independent
proof words enters once at its consuming stage. Fixed offsets map the standard
7856-byte signature into the typed witness. The independent wire parser rejects
other lengths. The measured transaction profile fixes empty context and obtains
its 32-byte message from native `sig_all_hash`; it does not take a trusted digest
hint. The official fixture below hashes its complete framed message in Simplicity.

## Official vector coverage

The [data manifest](../vendor-specs/slhdsa/MANIFEST.md) pins NIST ACVP commit
`975de31eb83d87039ec88934fdc47d8c312b892d`, source URLs and checksums. All **42**
SHA2-128s cases in its three groups are inventoried. The independent reference
passes **all 28 pure/internal cases**, comprising four expected accepts and
24 expected rejects, including malformed 7855/7857-byte signatures. Actual
exit status is 0; the complete results are in
[slh-dsa-standard-reference.txt](data/slh-dsa-standard-reference.txt) and its
separate status JSON. Fourteen pre-hash-interface cases are retained as data
but outside this pure baseline; they are not silently claimed as verified.

The deterministically selected Simplicity interoperability fixture is official
external-pure group 19, case 266: a 24-byte message, 255-byte context and
281-byte framed message. Its non-counted `upstreamCertificate` fixture checks
that signature plus three same-CMR corruptions. Seven additional derived
transaction vectors check the full native-message path and header/proof splices.
The official Simplicity fixture passed all four vectors (actual exit status 0,
802.738 seconds, maximum heap residency 9133865632 bytes under a 24 GiB cap).
The seven-vector native transaction group remains in progress. See
`slh-standard-verification-status.json` and the corresponding logs. A heap or
compilation failure is not a passing verifier result.

The derived fixture generator computes the top 512-leaf tree in full but uses
arbitrary lower authentication siblings for verification fixtures. It is not a
claim to reproduce standard key generation or signature generation. The official
ACVP fixture is the independent interoperability evidence.

## Reproduction

The full all-parameter prompt is kept out of the repository; its pinned URL,
30,513,796-byte length and SHA-256 are recorded in the manifest. Download it as
data, then reproduce the complete 128s selection:

```sh
python3 tools/extract_slh_acvp.py /path/to/official/prompt.json
```

The extractor rejects bytes with a different SHA-256. No downloaded code is
executed. `tools/SlhDsaStandardReference.hs` checks the complete supported
reference subset; `tools/WitnessBoundVerification.hs` exposes `slh-standard-kat`
and `slh-standard` groups for the compiled diagnostic. The large construction
is run sequentially with an explicitly recorded heap cap. Costs and feasibility
must come from the fresh in-tree runner, not from reference speed or GHC memory.
