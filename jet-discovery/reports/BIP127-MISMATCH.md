# BIP127 commitment hash: pinned BDK divergence

The normative BIP127 proof uses **single SHA256** for its prefixed message commitment. The pinned BDK implementation uses **SHA256d**. These create different commitment inputs and therefore different proof transactions and signature messages. This is an interoperability mismatch; it is not a claim that either hash choice loses message-binding security.

| Source | Pinned revision | Observed operation |
| --- | --- | --- |
| [BIP127 v1.0.0, Proof Format](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0127.mediawiki#proof-format) | `a0c977f3755da6476b955677ca9318334a2432c4` | SHA256 of UTF-8 `Proof-of-Reserves: ` followed by the commitment message; previous-output index0. The specification repeats the single-SHA operation in its PSBT signing requirements. |
| [BDK reserves constructor](https://github.com/bitcoindevkit/bdk-reserves/blob/a1621e6df959456f651fdd3c1bdadd2716109fa3/src/reserves.rs#L348-L355) | `a1621e6df959456f651fdd3c1bdadd2716109fa3` | Builds the same prefix, then calls `sha256d::Hash::hash(message.as_bytes())` and `Txid::from_raw_hash(message)`. |
| [BIP author's older reference constructor](https://github.com/stevenroose/reserves/blob/68f00a758d7e84e66e873f686ed1e02ba6f7e37f/src/bitcoin.rs#L99-L110) | `68f00a758d7e84e66e873f686ed1e02ba6f7e37f` | Calls its single-SHA256 helper and assigns those bytes to the previous txid. This historical prototype accepts a complete challenge string and is not claimed to implement all current BIP127 formatting rules. |

Both repositories were retrieved as inert archives; selected Rust/docs/license files were extracted as `.txt` research data. None was compiled, imported, or executed. Exact archive/member hashes and URLs are retained in [bitcoin-growth2/manifest.json](../vendor-specs/bitcoin-growth2/manifest.json).

For message `Some Message`, the exact prefixed UTF-8 payload gives:

| Field | Normative single SHA256 | Pinned BDK SHA256d |
| --- | --- | --- |
| Raw digest bytes | `30896246cd560f641d84e2ddcd9ee0f8fd74e4547be75aa7d6464f75dd372dff` | `bac9fc4e74693ce231c913edc8e31e18b8cf0195be8edf68974d8e67d117d1a7` |
| Reverse-byte txid display | `ff2d37dd754f46d6a75ae77b54e474fdf8e09ecddde2841d640f56cd46628930` | `a7d117d1678e4d9768df8ebe9501cfb8181ee3c8ed13c931e23c69744efcc9ba` |

The complete local comparison is in [bip127-commitment-comparison.json](../vendor-specs/bitcoin-growth2/bip127-commitment-comparison.json). It preserves the prefix/message bytes and source revisions. This comparison is derived evidence, not an upstream test vector or upstream execution.

The bounded new verifier will follow the normative **single-SHA256** statement. BDK-generated double-SHA commitments will be explicit negative compatibility cases. Upstream source and vectors are retained unchanged; no upstream correction is attempted. This note is separate from the shared mismatch report while the current milestone is being committed.
