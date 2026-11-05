# Documented eprint scan: 2020–2026

This is a complete, reproducible inventory of the metadata hits returned by the 14 queries below, followed by an explicitly automated first triage. It is not a claim of a full-text review of the whole archive. Every one of the 1,814 unique in-window hits has a row, title, authors, URL, matching query/queries, abstract snippet, metadata verdict and reason, plus reviewed verdict/program mappings for selected papers in the primary scan log, [`data/eprint-scan.tsv`](data/eprint-scan.tsv). The 33 source result pages and checksums are preserved under [`vendor-specs/eprint/`](../vendor-specs/eprint/MANIFEST.md).

## Coverage and retrieval

Search endpoint: `https://eprint.iacr.org/search`; each request uses `q=<query>&submittedafter=2019&submittedbefore=2027&offset=<0,100,...>`. The log independently filters paper IDs to 2020 through 2026 inclusive. Retrieval was 2026-11-04; 2026 is therefore partial through that date, not a claim to include the remainder of 2026. The search covers title, authors, abstract and keywords, with the archive's stemming; it does not search PDF full text. This distinction is stated in the search help preserved in each snapshot.

| Exact query | Result pages | Raw hits parsed | Unique hits in 2020–2026 |
| --- | ---: | ---: | ---: |
| `bitcoin` | 4 | 374 | 324 |
| `covenant` | 1 | 6 | 6 |
| `Schnorr` | 3 | 237 | 226 |
| `adaptor` | 1 | 59 | 58 |
| `threshold` | 12 | 1174 | 1105 |
| `"hash-based"` | 3 | 204 | 191 |
| `"post-quantum signatures"` | 2 | 109 | 104 |
| `BitVM` | 1 | 24 | 24 |
| `"payment channels"` | 1 | 65 | 59 |
| `ecash` | 1 | 4 | 4 |
| `"proof of reserves"` | 1 | 5 | 4 |
| `"proofs of reserves"` | 1 | 1 | 1 |
| `"blind Schnorr"` | 1 | 14 | 13 |
| `"timed signatures"` | 1 | 5 | 4 |

The script checks every page, parses every advertised hit, and refuses to silently continue on a missing page or inconsistent final count. The site rounds some initial totals to the next 100 (e.g. threshold displays 1200 until the last page reports 1174); the exact final-page total is checked against the number parsed. Search-query overlap is deduplicated by eprint ID, with all matching queries retained.

Reproduce with `python3 tools/eprint_scan.py --offline` using the snapshots; use `--refresh` to fetch current pages and intentionally replace the snapshot. Online retrieval uses curl because Python urllib receives HTTP403 at these endpoints. Requests are sequential and rate-spaced.

## Triage semantics

The log uses visible, deterministic metadata rules implemented in `tools/eprint_scan.py`, in this priority order:

1. `CANDIDATE`: bridge/dispute, signature, covenant, adaptor, channel or reserves relations with a plausible authorization/accountability use; implementation is not implied.
2. `EXCLUDE`: a clearly identified consensus/network/economic/attack topic without a new spending-condition verification relation.
3. `DEFER`: metadata does not settle a Bitcoin verification path, or a final Schnorr signature may already be covered by existing jets. These remain outstanding full-text reviews, not negative conclusions.

Counts: 148 candidate, 71 exclude, 1595 defer. The 1,595 deferred records are a material coverage gap. Candidate labeling can have false positives (for example a hash-signature attack paper); full-text review must refine that classification. No deferred record is silently dropped or presented as reviewed.

Seven individually reviewed ePrint verdicts are persisted in `data/eprint-reviewed.json` and merged into the TSV by the reproducer. They supplement, rather than erase, the automated first-pass classification. Blank reviewed columns explicitly mean no individual full-text implementation review is claimed.

## Reviewed implementation choices

| Scheme/source | Bitcoin deployment path | Corpus result or triage decision |
| --- | --- | --- |
| [BitVM, 2024/1995](https://eprint.iacr.org/2024/1995) | A pre-signed dispute transaction can require openings of fixed bit commitments and check one gate; revealing both labels enables a slashing branch. | `eprint-bitvm-nand-dispute` and `eprint-bitvm-equivocation-slash`; components explicitly labeled, not a complete bridge. Full Lamport OTS transaction authorization: `eprint-lamport-transaction-signature`. |
| [Blind Schnorr, 2022/1676](https://eprint.iacr.org/2022/1676) | Blind credentials/ecash can require issuer-response accountability, and the requester can check unblinding before accepting a token. | `eprint-blind-schnorr-response` checks the response, blinded challenge and final BIP340 equation. It implements the single-session algebra; the paper's NIZK/PKE concurrency machinery is not claimed. |
| [FROST, 2020/852](https://eprint.iacr.org/2020/852); [RFC9591](https://www.rfc-editor.org/rfc/rfc9591.txt) | Threshold custodians use partial-share checks to identify a faulty signing participant; the final aggregate signature already uses Schnorr verification. | `eprint-frost-signature-share` implements the share relation with coordinator challenge/binding/Lagrange factors as explicit inputs, not a full transcript generator. |
| [RFC8391 XMSS](https://www.rfc-editor.org/rfc/rfc8391.txt) and scan's hash-signature family | An output can directly require a hash-based signature on its transaction, provided the signer manages one-time leaf state. | `pq-xmss-sha2-10-256` implements 67 WOTS+ chains including checksum, randomized L-tree and height10 Merkle verification; `pq-lms-sha256-m32-h10` implements RFC8554 LMOTS/LMS with different domain-separated chains and public-key compression; existing SHRINCS/SLH-DSA entries provide other parameter families. XMSS uses derived vectors and has no checked upstream interoperability KAT. LMS passed the four-case fixture around the official RFC8554 Appendix F H10/W4 subkey certificate. The FIPS205 SHA2-128s baseline passed the four-case official Simplicity fixture and the independent reference checked all 28 supported official cases. These standard fixtures are separate from each program's derived transaction vectors. [LMS certificate evidence](data/lms-kat-witness-bound.txt), [SLH-DSA baseline](SLH-DSA-BASELINE.md). |
| [Verifiable Timed Signatures, 2020/1563](https://eprint.iacr.org/2020/1563) | Time-locking an off-chain signature has channel/fair-exchange uses. It differs from Bitcoin CLTV/CSV. | Defer: the homomorphic puzzle, cut-and-choose validity proof and extraction path are not implemented. A locktime check would not be an implementation of this construction. Exact remaining path: [timed-signatures.md](timed-signatures.md). |
| [On Proving Pairings, 2024/640](https://eprint.iacr.org/2024/640); [BitVM2, 2025/1158](https://eprint.iacr.org/2025/1158) | Groth16 bridge/dispute verification supplies a Bitcoin deployment path for BN254, reversing the earlier exclusion. | Two measured field kernels and an explicitly bounded arithmetic-component ESTIMATE; see [bn254-groth16.md](bn254-groth16.md). No complete pairing program is counted. |
| [Pairing zkSNARK in Script, 2024/1498](https://eprint.iacr.org/2024/1498) | Its stated deployment is BSV, whose script rules differ from Bitcoin. | Arithmetic reference only. Do not treat its BSV mainnet claim as BTC mainnet compatibility. |

## Remaining review and implementation gaps

The search is metadata-only and keyword-bounded. Papers lacking these terms, renamed schemes and relevant work outside 2020–2026 can be missed. Search snippets truncate abstracts, so the automated exclusion/candidate rules are provisional. Selected official metadata/RFC pages were inspected separately; no claim is made that all 1,814 PDFs were read. No upstream vectors were available for the newly derived BitVM/blinding examples; shared spec misunderstandings between reference and expression remain possible. The timed-signature validity proof, concurrent blind-signing wrapper, complete FROST transcript, complete optimized pairing verifier and the remaining candidate/deferred literature are still work to do.
