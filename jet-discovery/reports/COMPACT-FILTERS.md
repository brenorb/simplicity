# Complete bounded BIP157/158 compact-filter client

`app-bip157-158-filter-query` is one bounded client verifier for an authenticated filter-header checkpoint and a watched Bitcoin output script. It implements both the BIP157 filter-header relation and the actual BIP158 GCS query. Parameters, block rows, match/nonmatch answers and codec helpers do not earn separate groups. The final nine-vector suite and52 native source/boundary cases pass; the entry is ready for shared integration.

The primary specifications are [BIP157](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0157.mediawiki) and [BIP158](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0158.mediawiki), CC0-1.0. Their exact source texts are frozen in Growth3. The full [official testnet JSON](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0158/testnet-19.json), not a sample, is retained in Growth4. The prose says “five” testnet blocks, while the actual pinned JSON contains ten data rows. All ten are inventoried and checked; its one header row is not a vector. The JSON has no separate embedded license; its publication alongside the CC0 BIP is recorded explicitly.

The client must authenticate the association of block hash, previous filter header, expected current filter header and watched script. These are committed program parameters. BIP157 filter headers are **not Bitcoin consensus commitments**: checkpoint trust, peer agreement/disagreement resolution, full-block recomputation to identify a faulty peer, Bitcoin chain/finality authentication and the completeness/correctness of the source filter remain external client duties. This predicate does not prove a payment, absence of a transaction, or full-block validity. A match can be a BIP158 false positive and triggers a full-block download; the nominal per-item false-positive probability is1/784931.

The kernel checks `SHA256d(SHA256d(serialized_filter) || previous_raw_filter_header) == expected_raw_filter_header`, then fully parses the same actual bytes. It decodes every unary quotient and19-bit remainder, adds deltas with overflow checks, requires each cumulative value in `[0,N*784931)`, and compares the target from the **high64 bits** of `SipHash24(k, script) * (N*784931)`. The keys are the first16 raw block-hash bytes interpreted as two little-endian64-bit integers. It parses all values, rather than stopping at the first match, to check canonical zero padding and exact byte length. Empty filters have one zero byte and cannot match.

`Ref.CompactFilters.displayHashToRaw` and `rawHashToDisplay` are the only explorer/display conversions. `blockHashRaw` returns the untouched double-SHA256 digest of the actual80-byte header. Raw digest/filter/header bytes are never reversed inside the native kernel. Every official header independently matches its display block hash, and every official filter header matches double hashing of raw concatenated fields. This distinguishes the public display boundary from the native opHash convention repaired in `OUTPOINT-BYTEORDER.md`.

The bound is `N<=16`, one watched script<=511 bytes and canonical filters<=44 bytes. Since the sum of all deltas is less than `16*784931`, the total unary quotients are at most23. Thus the encoded payload has at most `20*16+23=343` bits, or43 bytes, plus one CompactSize count byte. A quotient24 cannot be valid inside the bound. The program checks the remaining-bit count before every read and rejects unused nonzero bits, extra zero bytes, truncated codes and any count above16.

One structured witness `(byte_length8, left_aligned_raw_word512)` enters once through `boundProgram`; all hash/parser/match reuse follows projections of that actual value. Every bit outside the declared bytes must be zero. This fixed520-bit native witness representation is65 bytes; it is a checked typed representation of the original network filter, not a claim that its physical Simplicity witness has the same length as the network bytes. Its SHA256 routine builds the correct one-block byte padding and length. The `Assert` kernel contains no Witness nodes. The Bitcoin primitive environment is unused, and budget comparisons do not imply an onchain spending path.

| Official row | Testnet height | N | Filter bytes | Full block bytes | Previous-output scripts | Source/native coverage |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
|0|0|1|4|285|0|Exact bytes/header; match/nonmatch; malformed and false claim|
|1|2|1|4|190|0|Same complete checks|
|2|3|1|4|190|0|Same complete checks|
|3|15007|1|4|190|0|OP_RETURN followed by opcodes excluded correctly|
|4|49291|10|28|1597|8|Empty output script excluded correctly|
|5|180480|13|35|1344|8|Spent empty script excluded; complete registered fixture|
|6|926485|9|25|1982|8|Duplicate item removed before hashing|
|7|987876|1|4|193|0|Unparseable output script retained as raw bytes|
|8|1263442|3|9|518|1|Actual witness transaction parsed|
|9|1414221|0|1|165|0|Exact empty filter and nonmatch behavior|

`extract_bip158_vectors.py` parses every full block and all supplied previous-output scripts, constructs the exact unique nonempty/non-OP_RETURN basic-filter set and checks raw header digests/counts. It writes the full ten-row `bip158-all-vectors.tsv` with every hash, header, filter and item. The independent byte/Integer reference reconstructs **every filter byte and filter header** and queries every actual item. No downloaded generator or other external code is executed. The reference log is `data/compact-filters-reference-rts.txt`.

The actual Simplicity source driver checks52 component cases: a match/nonmatch pair for every official row (two nonmatches for the empty row), two malformed-code cases per row authenticated with their **own fresh valid filter-header hash**, ten false membership claims, and derived maximum `N16/44-byte/quotient23` plus quotient24 rejection. This prevents a bad header hash from masking a decoder failure. The maximum-bound case is a derived canonical GCS stress input, not an invented published Bitcoin block or evidence of its filter completeness.

| Complete registered-profile vector | Expected |
| --- | --- |
| Official13-item filter at height180480, authenticated matching script | Accept |
| Actual raw filter data bit changed | Reject |
| Canonical filter from another real source block | Reject |
| Declared raw length truncated | Reject |
| Extra zero byte disguised as padding | Reject |
| N17 exceeds complete bound | Reject |
| Declared length zero | Reject |
| Declared length45 exceeds single-block bound | Reject |
| Nonzero data beyond declared raw bytes | Reject |

The preliminary eight-vector suite passed with exact per-vector CMR `78695ebedc110525a6af5c4caf49464502cdf61ba3b431868d78421f1d7a5fd5`,79.385 seconds elapsed,1,127,568,608 maximum live bytes and2261MiB total RTS memory at `-N1 -M3G -s`. Its immutable source/binary/log provenance is `data/compact-filters-prefinal-provenance.json`. The final nine-vector suite adds the explicit N17 rejection and the two native maximum-bound component checks without changing the kernel/CMR. All9 prepared results and52 source/boundary checks pass, exit0, with the same CMR. The final run took84.472 seconds,1,186,328,064 maximum live bytes and2698MiB total RTS memory at `-N1 -M3G -s`. Its exact source/object/driver snapshots, binary/log and packet hashes are `data/compact-filters-final-provenance.json` and `compact-filters-final-freeze/`. These are execution/CMR results, not a full-corpus cost measurement.

Reproduction: run `python3 tools/extract_bip158_vectors.py`; compile/run `CompactFiltersReference.hs`; compile `CompactFiltersSmoke.hs` against the cached GHC9.8.4 package database with `-O1 -threaded -rtsopts -isrc`, then run `+RTS -N1 -M3G -s`. To reproduce the frozen run directly, use `-ireports/data/compact-filters-final-freeze/src` and `reports/data/compact-filters-final-freeze/tools/CompactFiltersSmoke.hs` in place of the live source/driver. The final source freeze and exact binary/log/data hashes are in `data/compact-filters-final-provenance.json`; `python3 tools/check_bitcoin_growth4_packet.py` verifies every primary/derived artifact, cross-packet source hash and LF TSV offline. No shared registry/Cabal/test files are edited by these tools.
