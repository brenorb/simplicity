# Pinned BIP and no-number proposal sources

This directory is research data. No upstream code is executed or compiled.

- `README.mediawiki`: the complete `bitcoin/bips` index at commit
  `a0c977f3755da6476b955677ca9318334a2432c4`, observed 2026-11-04.
- `revision.json`, `tree.json`: GitHub commit/tree metadata for that revision.
- `index-all.tsv`: all 220 indexed numbered rows, including allocated numbers.
- `softfork-triage.tsv`: all 51 softfork rows, with nonterminal scope decisions.
- `upstream/`: every nonterminal softfork specification and the text/data/vector
  assets under its BIP directory (46 files).
- `manifest.json`: immutable source URLs, Git blob IDs, SHA-256 hashes, sizes and
  per-BIP license declarations for those 46 files. Licensing remains per file;
  there is no single replacement license for the directory.
- `proposals/sources.json`: URLs, revisions/message IDs, license statements or
  explicit absence of a statement, SHA-256 hashes and sizes for 17 additional
  public proposal snapshots. Forum, API and HackMD responses can change; their
  hashes identify the observed bytes, not an immutable upstream revision.

The human-readable audit, coverage and implementation gaps are in
[BIP-INVENTORY.md](../../reports/BIP-INVENTORY.md). In particular, downloaded
vectors are distinguished from executed vectors. Not every full Script,
wallet or transaction-wide consensus behavior is within the corpus harness.

From `jet-discovery/`, audit all downloaded specification/vector blobs and
additional proposal snapshots without a network connection:

```sh
python3 tools/fetch_bip_inventory.py --offline
python3 tools/fetch_proposal_sources.py --offline
python3 tools/extract_bip360_vectors.py
```

The BIP fetcher also supports downloading the immutable snapshot. The proposal
fetcher checks new responses against the recorded hashes and refuses to
overwrite an archived snapshot if an upstream mutable page has changed.
