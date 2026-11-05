# Period gas/compute ranking supplement

The complete **Soltop top-20 Solana programs by provider-reported last-24h CU** is now captured. This improves the period coverage beyond the existing complete one-slot sample. Etherscan's Ethereum period ranking and Solscan's top-100 dataset remain access gaps. A separate [complete Ethereum UTC-day chain-derived ranking](ETHEREUM-DAY-GAS-RANKING.md) now covers 2026-11-04 and reconciles every block and receipt. Soltop is a separate operator/data collector; this is not a recovered Solscan dataset. Existing chain snapshots and TVL lists in [contract-inventory.md](contract-inventory.md) are preserved.

## Source, period and coverage

| Field | Captured evidence |
| --- | --- |
| Chain | Solana mainnet-beta; the provider's homepage identifies Solana Mainnet. No devnet/testnet endpoint was substituted. |
| Operator/API | [Soltop Analytics API](https://soltop.sh/docs/index.html), schema version 0.6.0; [complete ranking response endpoint](https://api.soltop.sh/api/top-programs). Anonymous access, no account or API key. |
| Ranking period | API documentation specifies the last 24 hours. The response itself contains no start/end timestamps, block/slot bounds, update timestamp, coverage count or pagination token. Exact ranking cutoffs and ingestion completeness therefore remain unknown. |
| Capture time | Request started **2026-11-05 08:23:43.249388 UTC**, finished **08:23:43.519531 UTC**; HTTP `Date` **08:23:43 GMT**, `X-Cache: MISS`, advertised cache maximum age 30 seconds. Request time is not asserted to be the exact data cutoff. |
| Full requested result | All **20/20** rows of the endpoint's documented fixed top-20 result, without sampling or truncation. It is not the full universe of programs. No alternative period or larger limit is documented for this endpoint. |
| Metric | Exact source field `total_cu_consumed`, sorted descending. Additional source fields `transaction_count`, `avg_cu_per_transaction`, `success_rate` are retained in full. This is CU, not fee revenue, token value, allocated CU, or transaction volume used as a proxy for CU. |
| Validation | Twenty distinct valid 32-byte base58 program IDs; descending nonnegative CU; source average equals CU/count within 0.000001 CU; success rates in 0–100. These checks validate the downloaded table, not the provider's chain ingestion. |
| Matching network time series | Separate request returned **10,801 distinct contiguous 8-second bucket labels**, oldest **2026-11-04 08:23:36**, newest **2026-11-05 08:23:36**, exactly 86,400 seconds apart. Labels carry no timezone suffix. They establish the network series' reported span, not the separate ranking query's exact cutoffs or atomicity. |
| Separate summary | Provider-reported `total_cu_24h = 8,613,982,398,738`, `active_programs_24h = 3,427`, `avg_success_rate_24h = 75.83959510156767`. It is a separate response; no network-share percentage is inferred from it. |
| Sum of listed rows | **6,016,077,872,868 provider-reported CU** across the 20 returned entries. This is not described as exclusive network CU. |
| Raw files | [Manifest](../vendor-specs/rankings/soltop-2026-11-05/manifest.json), [JSON table](../vendor-specs/rankings/soltop-2026-11-05/top-programs.json), [full-precision TSV](../vendor-specs/rankings/soltop-2026-11-05/top20.tsv), [network buckets](../vendor-specs/rankings/soltop-2026-11-05/timeseries.json), [validation](../vendor-specs/rankings/soltop-2026-11-05/validation.json). |

The deployed API's nested-CPI accounting, missing/truncated-log handling, failed-transaction handling, slot completeness, and ingestion lag are not specified by the public API schema. The related [open-source TUI parser](https://github.com/soltop-app/soltop-oss/blob/7a4ac0103af807380441e258adca3d3f78300738/src/rpc/parser.rs) sums all matching `Program … consumed` log records and does not subtract nested invocations; its README warns that incomplete program logs can omit CU. **Equivalence between that parser and the deployed analytics API has not been established.** Consequently, this table must not be treated as exclusive CU or numerically combined with the existing one-slot exclusive-CU allocation. The related TUI source is pinned as methodological context, not as proof of the deployed backend's implementation.

## Complete top-20 and UTXO triage

CU/count values are exact integers. Average CU and success percentages are displayed to two decimal places here; the TSV retains source precision. `Count` means the API's `transaction_count` field; distinct-transaction deduplication has not been independently verified. Program labels describe deployment identities, not a claim that a complete port has been implemented. Unknown programs remain source-analysis gaps.

| Rank | Program | Label | Reported CU, 24h | Count | Average CU | Success % | UTXO verdict / reason |
| ---: | --- | --- | ---: | ---: | ---: | ---: | --- |
| 1 | `pAMMBay6oceH9fJKBRHGP5D4bD4sWpmSwMn52FMfXEA` | PumpSwap AMM | 1,515,734,736,354 | 39,273,855 | 38,593.99 | 86.34 | Partial fit: reserve arithmetic and output allocation can constrain a pool UTXO; explicit assets and serialized state required. |
| 2 | `JUP6LkbZbjS1jKKwapdHNy74zcZ3tLUZoi5QNyVTaV4` | Jupiter v6 aggregator | 814,638,049,879 | 17,563,923 | 46,381.33 | 35.92 | Partial fit: a bounded chosen swap route can constrain its inputs/outputs; general cross-program routing and mutable accounts need separately committed pool states. |
| 3 | `ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL` | SPL Associated Token Account | 701,815,273,592 | 52,979,480 | 13,246.93 | 80.28 | Not directly applicable: Solana account-address derivation; Bitcoin outputs already encode ownership. Not a separate Bitcoin application. |
| 4 | `6EF8rrecthR5Dkzon8Nwu78hRvfCKubJ14M5uBEwF6P` | Pump.fun | 405,993,522,931 | 12,315,186 | 32,966.90 | 79.21 | Partial fit: bonding-curve arithmetic and payout covenant; token supply and mint state need explicit asset semantics. |
| 5 | `EtrnLzgbS7nMMy5fbD42kXiUzGg8XQzJ972Xtk1cjWih` | Unclassified program | 309,412,322,728 | 15,690,641 | 19,719.55 | 87.84 | Analysis gap: no verified implementation identified; CU and a program ID do not determine a Bitcoin spending predicate. |
| 6 | `TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb` | SPL Token-2022 | 261,066,806,640 | 104,894,857 | 2,488.84 | 78.06 | Partial fit: transfer authorization is a UTXO predicate; token extensions and supply require explicit asset and state semantics. |
| 7 | `LBUZKhRxPF3XUpBCjp4YzTKgLccjZhTSDM9YuVaPwxo` | Meteora DLMM | 211,519,169,966 | 10,639,689 | 19,880.20 | 46.82 | Partial fit: bin-based price/liquidity/fee arithmetic and reserve outputs can constrain a bounded pool-state transition; not the whole dynamic account program. |
| 8 | `HgFifdfTMQY7F2F6JeVi4xJbWGenycD91jwh2iFo4fTc` | Unclassified program | 177,293,932,959 | 5,616,211 | 31,568.25 | 100.00 | Analysis gap: no verified implementation identified; CU and a program ID do not determine a Bitcoin spending predicate. |
| 9 | `6Vo3245eszAb5wuqEMw8mGdbfRUdKbHhDHP5LcaGuTAB` | Unclassified program | 167,799,776,085 | 1,052,535 | 159,424.41 | 95.02 | Analysis gap: no verified implementation identified; CU and a program ID do not determine a Bitcoin spending predicate. |
| 10 | `DF1ow4tspfHX9JwWJsAb9epbkA8hmpSEAtxXy1V27QBH` | Unclassified program | 159,936,370,762 | 2,907,383 | 55,010.42 | 85.67 | Analysis gap: no verified implementation identified; CU and a program ID do not determine a Bitcoin spending predicate. |
| 11 | `2vMRKW921MjQuUTAc2MdheBCHhSXHHGcKw2SLKtMyz8S` | Unclassified program | 154,730,508,073 | 5,621,670 | 27,523.94 | 100.00 | Analysis gap: no verified implementation identified; CU and a program ID do not determine a Bitcoin spending predicate. |
| 12 | `TessVdML9pBGgG9yGks7o4HewRaXVAMuoVj4x83GLQH` | Unclassified program | 153,076,235,944 | 8,120,057 | 18,851.62 | 66.29 | Analysis gap: no verified implementation identified; CU and a program ID do not determine a Bitcoin spending predicate. |
| 13 | `CAMMCzo5YL8w4VFF8KVHrK22GGUsp5VTaW7grrKgrWqK` | Raydium CLMM | 149,069,367,456 | 2,929,054 | 50,893.35 | 52.84 | Partial fit: tick arithmetic, reserve outputs and per-position state can constrain a serialized pool UTXO; explicit assets required. |
| 14 | `BiSoNHVpsVZW2F7rx2eQ59yQwKxzU5NvBcmKshCSUypi` | Unclassified program | 144,200,139,622 | 4,771,476 | 30,221.29 | 43.34 | Analysis gap: no verified implementation identified; CU and a program ID do not determine a Bitcoin spending predicate. |
| 15 | `whirLbMiicVdio4qvUfM5KAg6Ct8VwpYzGff3uctyCc` | Orca Whirlpool | 137,033,853,409 | 3,755,864 | 36,485.31 | 57.24 | Partial fit: concentrated-liquidity tick arithmetic and per-position state fit a serialized pool UTXO with explicit assets. |
| 16 | `MAyhSmzXzV1pTf7LsNkrNwkWKTo4ougAJ1PPg47MD4e` | Unclassified program | 120,493,546,399 | 1,969,771 | 61,171.35 | 99.39 | Analysis gap: no verified implementation identified; CU and a program ID do not determine a Bitcoin spending predicate. |
| 17 | `FLASHX8DrLbgeR8FcfNV1F5krxYcYMUdBkrP1EPBtxB9` | Unclassified program | 113,832,187,212 | 4,343,288 | 26,208.76 | 97.82 | Analysis gap: no verified implementation identified; CU and a program ID do not determine a Bitcoin spending predicate. |
| 18 | `pfeeUxB6jkeY1Hxd7CsFCAjcbHA9rWtchMGdZ6VojVZ` | Pump fee program | 107,461,798,472 | 19,158,286 | 5,609.16 | 82.96 | Partial fit: fee computation and recipient payout splitting fit an output covenant; dynamic configuration must be committed or authenticated. |
| 19 | `DiabLokxisGR8P4Qqp2QL6PmBhhVsdzPstCE4WoLxc5z` | Unclassified program | 106,318,771,031 | 2,189,671 | 48,554.68 | 77.33 | Analysis gap: no verified implementation identified; CU and a program ID do not determine a Bitcoin spending predicate. |
| 20 | `B3111yJCeHBcA1bizdJjUFPALfhAfSRnAbJzGUtnt56A` | Unclassified program | 104,651,503,354 | 426,177 | 245,558.78 | 18.88 | Analysis gap: no verified implementation identified; CU and a program ID do not determine a Bitcoin spending predicate. |

Labels and existing mapping evidence for PumpSwap, Pump.fun, SPL ATA, Token-2022, Orca and Pump fees are carried from [the primary-source inventory](contract-inventory.md#label-sources-and-licensing). Newly identified labels use pinned primary sources: [Jupiter v6 parser README](https://github.com/jup-ag/instruction-parser/blob/e6f77951377847c579112e6a16d8c17c5c092485/README.md), [Meteora DLMM guide](https://github.com/MeteoraAg/docs/blob/edf57ecf775ffeb20aabbe80bfa1b1dd70be3493/developer-guides/dlmm/index.mdx), and [Raydium library deployment table](https://github.com/raydium-io/raydium-library/blob/72a22dcd6136fdd354c47d35aaa4b035652398c5/README.md). These nine labeled entries receive a mapping verdict; all eleven unclassified entries receive an explicit analysis gap. No additional corpus program is counted by this report.

## Access gaps and rejected substitutions

| Requested source/path | Observed result | Coverage consequence |
| --- | --- | --- |
| [Etherscan Gas Tracker, 24h sort](https://etherscan.io/gastracker?gasperiodsort=24) | HTTP 403 via direct retrieval and web tool. New captured attempt **2026-11-05 08:23:44 UTC**; body/hash/headers in manifest. `/topstat` also HTTP 403. | No complete current Ethereum 24h/7d per-contract gas ranking obtained. Existing complete Ethereum block **26,346,924** remains the reproducible gas snapshot. |
| Search-engine Etherscan extraction | Partial cached rows, reported crawls about three months old; displayed update blocks around 25.59–25.61 million. | Incomplete, stale, and no precise period cutoff. Not promoted to a full or current ranking; no cached partial table substitutes for the requested complete set. |
| [Solscan Fee Tracker](https://solscan.io/analysis/fee-tracker) | Earlier attempts HTTP 403; captured static page at **08:23:44 UTC** returned HTTP 200. It contains table headers/empty state and `pageProps: {}`; no program rows. | HTTP success does not recover the dataset. |
| [Actual Solscan 24h dashboard data query](https://api-v2.solscan.io/v2/analytics/fee_tracker/dashboard?chart_type=TOP_PROGRAMS_CONSUME_FEE_24H) | Identified from the site's referenced production app/config and dashboard chunk, inspected only as inert text. Public unauthenticated query returned Cloudflare HTTP 403; body/hash/headers retained. | Full top-100 rows unavailable. The documented candidate set is fee-ranked and carries CU columns; even a recovered list would not automatically establish the global top 100 by CU. |
| [Solscan Fee Tracker guide](https://kb.solscan.io/solscan-fee-tracker-dashboard) | Official guide describes top 100 programs, 3h/24h fee and CU columns; percentages use totals of those 100, not whole-network totals. | Definition evidence only, not data. It cannot supply missing program rows or exact cutoffs. |
| [Solscan compute analytics API documentation](https://pro-api.solscan.io/pro-api-docs/v2.0/ref/analytics-compute-units) | Describes daily network-total CU series rather than a program ranking. | Not substituted for per-program compute use. |
| [ultrasound.money](https://ultrasound.money/) | Public page/extracted content provides burn-oriented material; no complete per-contract raw-gas 24h/7d table retrieved in this audit. | ETH burned is base-fee-weighted gas and cannot silently replace gas units. No burn ranking is reported as a gas ranking. |
| Other Etherscan-family explorers / DeFi fee datasets | Search results included other chains and protocol fee/revenue tables. | Wrong-chain tables and protocol fee USD are excluded. |

No seven-day program ranking and no independently reconciled Solana 24h ledger aggregate have been established. Ethereum has the separate complete UTC-day result linked above. The accessible Soltop dataset supplies a complete *provider-reported* 24h top list with the limitations above; the existing independent block snapshots remain useful complementary evidence.

## Reproduction and licensing

From `jet-discovery/`, validate the captured bytes, table and bucket coverage without network access:

```sh
python3 tools/fetch_period_rankings.py --check vendor-specs/rankings/soltop-2026-11-05
```

To capture a new public observation, choose a **new** output directory:

```sh
python3 tools/fetch_period_rankings.py --fetch vendor-specs/rankings/soltop-NEW-CAPTURE
```

The script refuses an existing output directory. Live values will change. It records exact URL, request bounds, HTTP status/headers, byte length, SHA256, explicit pinned source revision where available, and license status. IP literals in HTTP 403 failure pages are redacted; original-response and archived-byte hashes/lengths are both recorded. Successful JSON responses are unchanged. The live API/schema revision is not an immutable source commit; their byte hashes identify the captured revision. The related Soltop source revision is **7a4ac0103af807380441e258adca3d3f78300738** and its MIT license is retained. No API-data or website-documentation license is inferred from source-code licensing. The two attempted protocol-library `LICENSE` paths returned 404 and are retained as access evidence, not license grants. Downloaded JavaScript/Rust/Markdown is data and is never imported, built, or executed by the harness.
