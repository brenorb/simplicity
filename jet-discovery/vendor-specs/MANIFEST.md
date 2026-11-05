# Vendored specifications and test vectors

These files are **data**. They are never compiled or executed. Each was downloaded verbatim from its source.

## bitcoin/bips

Source: https://github.com/bitcoin/bips at commit `5aadddb511a5dcfe4599531bd8ae5e5b96d0f793` (fetched 2026-11-02).
Each local filename is the upstream path with `/` replaced by `_`.

| file | upstream path | license (from BIP header) | sha256 |
| --- | --- | --- | --- |
| `bips/bip-0118.mediawiki` | `bip-0118.mediawiki` | BSD-3-Clause | `26a9e7d26b727572…` |
| `bips/bip-0119.mediawiki` | `bip-0119.mediawiki` | BSD-3-Clause | `8178117f76cea0fe…` |
| `bips/bip-0119_vectors_ctvhash.json` | `bip-0119/vectors/ctvhash.json` | BSD-3-Clause | `3cff1abe3284b9d0…` |
| `bips/bip-0340.mediawiki` | `bip-0340.mediawiki` | BSD-2-Clause | `17d64d6dc6bc97f4…` |
| `bips/bip-0340_test-vectors.csv` | `bip-0340/test-vectors.csv` | BSD-2-Clause | `34c9d1d9c3a88d52…` |
| `bips/bip-0345.mediawiki` | `bip-0345.mediawiki` | BSD-3-Clause | `3b34c99f269d2890…` |
| `bips/bip-0346.md` | `bip-0346.md` | BSD-3-Clause | `2c37a344e7dea50c…` |
| `bips/bip-0346_ref-impl_txhash_vectors.json` | `bip-0346/ref-impl/txhash_vectors.json` | BSD-3-Clause | `0bb35e5489092435…` |
| `bips/bip-0347.mediawiki` | `bip-0347.mediawiki` | BSD-3-Clause | `a95f3d3c305fb098…` |
| `bips/bip-0348.md` | `bip-0348.md` | BSD-3-Clause | `be997f3f5ab4d415…` |
| `bips/bip-0349.md` | `bip-0349.md` | BSD-3-Clause | `e73e7e440e66839a…` |
| `bips/bip-0442.md` | `bip-0442.md` | BSD-3-Clause | `9fbe121bcd9cc70c…` |
| `bips/bip-0443.mediawiki` | `bip-0443.mediawiki` | BSD-3-Clause | `53f4b9a7135d19be…` |
| `bips/bip-0446.md` | `bip-0446.md` | CC0-1.0 | `24dda2500618cfcc…` |
| `bips/bip-0446_README.md` | `bip-0446/README.md` | CC0-1.0 | `6763c67fb46b4e46…` |
| `bips/bip-0446_basics.json` | `bip-0446/basics.json` | CC0-1.0 | `19cd88462784a67e…` |
| `bips/bip-0448.md` | `bip-0448.md` | CC0-1.0 | `3b3addc6fe73f66c…` |

Fetched 2026-11-03 at bitcoin/bips commit `ada341963ab3916e74c98e6de4ba48babc024a75`:

| file | upstream path | license | sha256 |
| --- | --- | --- | --- |
| `bips/bip-0098.mediawiki` | `bip-0098.mediawiki` | CC-BY-SA-4.0 | `88e278277090e4b6…` |
| `bips/bip-0116.mediawiki` | `bip-0116.mediawiki` | CC-BY-SA-4.0 | `56c5e89285d773fc…` |
| `bips/bip-0117.mediawiki` | `bip-0117.mediawiki` | CC-BY-SA-4.0 | `6d01347ede4db133…` |
| `bips/bip-0360.mediawiki` | `bip-0360.mediawiki` | BSD-3-Clause | `988957d7373b3779…` |
| `bips/bip-0440.mediawiki` | `bip-0440.mediawiki` | BSD-3-Clause | `85e45b233d45bf21…` |
| `bips/bip-0441.mediawiki` | `bip-0441.mediawiki` | BSD-3-Clause | `6150cfc30776276b…` |
| `bips/bip-0449.md` | `bip-0449.md` | BSD-3-Clause | `a62ca765f6a37e21…` |
| `bips/bip-0327.mediawiki` | `bip-0327.mediawiki` | BSD-3-Clause | `918555f9d67bf4c1…` |
| `bips/bip-0327_vectors_key_agg_vectors.json` | `bip-0327/vectors/key_agg_vectors.json` | BSD-3-Clause | `03c02a97e4ef3f2e…` |
| `bips/bip-0346_ref-impl_src_main.rs` | `bip-0346/ref-impl/src/main.rs` | BSD-3-Clause (BIP 346); read as data and transcribed, never compiled | `92608ad4e0d32e33…` |

## SHRINCS/shrincs-bip

Source: https://github.com/SHRINCS/shrincs-bip at commit `4fe68e3a68fd58be6b0e19436ff6fb7a3357a291` (fetched 2026-11-02).
License: CC0-1.0 or MIT (per SHRINCS.md).  `gen_test_vectors.py` is kept as documentation only and is never executed;
the upstream test vectors are published only as SHA-256 fingerprints (`*.csv.fp`).

| file | upstream path | sha256 |
| --- | --- | --- |
| `shrincs/README.md` | `README.md` | `8bb74f013a0d97e8…` |
| `shrincs/SHRINCS.md` | `SHRINCS.md` | `7dcd7031e1985fa9…` |
| `shrincs/gen_test_vectors.py` | `gen_test_vectors.py` | `b69fc91bf1eae6fe…` |
| `shrincs/test_vectors_keygen.csv.fp` | `test_vectors/keygen.csv.fp` | `d5bec2685ef89f73…` |
| `shrincs/test_vectors_signatures_valid.csv.fp` | `test_vectors/signatures_valid.csv.fp` | `81b3444eb39171e7…` |

## RFCs

| file | source | license | sha256 |
| --- | --- | --- | --- |
| `rfc/rfc7693.txt` | https://www.rfc-editor.org/rfc/rfc7693.txt (fetched 2026-11-02) | IETF Trust (informational RFC) | `c943754888364fe2…` |
| `rfc/rfc6979.txt` | https://www.rfc-editor.org/rfc/rfc6979.txt (fetched 2026-11-03) | IETF Trust (informational RFC) | `456e8f17558fdbd2…` |
| `rfc/rfc8032.txt` | https://www.rfc-editor.org/rfc/rfc8032.txt (fetched 2026-11-03) | IETF Trust (informational RFC) | `ed63657ff3893012…` |

## Expanded source inventories (2026-11-04)

The following manifests carry complete hashes, immutable revisions where
available, licenses, coverage bounds, and access gaps. Downloaded code remains
specification data and is never imported, compiled, or executed.

- [BIP/proposal inventory](bip-inventory/README.md), with all 220 index rows,
  all 51 softfork rows, 46 pinned BIP data files and 17 proposal snapshots.
- [eprint and RFC sources](eprint/MANIFEST.md), including all 33 search-result
  pages for the documented 2020–2026 metadata scan, plus XMSS/LMS sources.
- [STARK protocol provenance](stark/MANIFEST.md), including the explicit
  DEEP-FRI PDF retrieval gap.
- [Ethereum/Solana source provenance](contracts/spec-provenance.json),
  [snapshot provenance](contracts/snapshot-provenance.json), and
  [snapshot hashes](contracts/snapshot-hashes.json).
