# Follow-up external material

External material added after the frozen evidence run. It is kept outside
`vendor-specs/` because `sourceFingerprint` (src/JetDiscovery/Snapshot.hs)
hashes that tree: adding files there would invalidate the frozen run's local
audit. Everything here is data. No downloaded code is executed, and none of it
is on the Haskell or C build path.

## BN254 precompile vectors (`bn254/`)

go-ethereum precompile test data, retrieved 2026-11-09 at commit
`7272636030a9c149c1f265a70008a5f2e813531e` from
`https://raw.githubusercontent.com/ethereum/go-ethereum/<commit>/core/vm/testdata/precompiles/<file>`.
License: go-ethereum library code and test data are LGPL-3.0 (`COPYING.LESSER`
in that repository). The files are stored unmodified.

| File | Vectors | SHA-256 |
| --- | ---: | --- |
| `bn256Add.json` | 16 | `a5e6e81aceb187e41006a14583a7feebcb03060f9b9f083613271477b9091fae` |
| `bn256ScalarMul.json` | 19 | `aed562c718b07d13363748b1311614b5c709b9517a230eb86e347c78bfbdae19` |
| `bn256Pairing.json` | 14 | `1011b31345f6470ebc409b674f0f4a9318ac23e9a0fab5052aee3b77901310f1` |

`tools/bn254_vectors.py` applies the EVM calldata padding/truncation and writes
`reports/data/followup-bn254-vectors.tsv`.

## eprint metadata pages (`eprint/abstracts/`)

The full eprint metadata page (title, authors, complete abstract, keywords,
category, license) of every record that the frozen scan left as `DEFER`. They
are fetched by `tools/eprint_abstracts.py` from `https://eprint.iacr.org/<year>/<n>`,
sequentially and rate-spaced. `abstracts/manifest.json` gives each page's URL,
retrieval time, byte count and SHA-256. Pages are stored unmodified. Individual
papers keep the licenses stated on their pages; eprint states no blanket license
for its HTML.
