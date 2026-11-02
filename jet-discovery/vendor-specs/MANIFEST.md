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
