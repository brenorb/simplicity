# Supplemental period rankings

`soltop-2026-11-05/` preserves a complete anonymous Soltop Analytics API top-20
Solana mainnet program list, advertised as compute consumed over the last 24 hours.
The ranking was captured at 2026-11-05 08:23:43 UTC. The accompanying network
time series has 10,801 contiguous eight-second labels spanning exactly 24 hours.
Its labels do not establish the ranking response's exact time cutoffs.

See [the full table, program triage, source definitions and access gaps](../../reports/PERIOD-RANKINGS.md).
This is provider-reported CU, with deployed nested-invocation accounting and
ledger completeness unknown; it is not numerically interchangeable with the
existing independently allocated exclusive-CU one-slot snapshot.

`manifest.json` records URLs, request bounds, HTTP metadata, pinned source
revisions, byte counts, SHA256 and license evidence. The successful ranking,
summary and network-series JSON are unchanged response bytes. IP literals in
403 failure pages are redacted; both original-response and archived-byte hashes
and lengths are recorded. `top20.tsv`, `validation.json` and `utxo-triage.tsv`
are local derivatives. All 20 IDs have triage, including 11 explicitly
unclassified programs.

Soltop's related TUI source is MIT-licensed. Its source-code license does not
establish a license for API data, hosted documentation or frontend assets.
Missing protocol-library `LICENSE` URLs returned 404 and are retained as
failures. JavaScript and Rust snapshots use `.txt` suffixes and are inert
research evidence, never harness build inputs. No downloaded source is executed.

Offline integrity and coverage check:

```sh
python3 tools/fetch_period_rankings.py --check vendor-specs/rankings/soltop-2026-11-05
```

New captures require a new output directory:

```sh
python3 tools/fetch_period_rankings.py --fetch vendor-specs/rankings/soltop-NEW-CAPTURE
```
