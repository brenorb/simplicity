# Complete bounded BIP152 compact-block reconstruction client

`app-bip152-compact-block-reconstruction` completes a bounded compact-block reconstruction from either an actual mempool transaction or a complete getblocktxn/blocktxn exchange. All13 functional evaluations and all13 prepared evaluations with per-vector canonical CMR checks pass. This is one client application group; the two fill paths, codecs, nonce changes and source procedures add no groups.

The primary specification is [BIP152](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0152.mediawiki), public domain. The official [Bitcoin Core v30.0 reference](https://github.com/bitcoin/bitcoin/blob/d0f6d9953a15d7c7111d46dcb76ab2bb18e5dee3/src/blockencodings.cpp), header and complete test source are pinned at `d0f6d9953a15d7c7111d46dcb76ab2bb18e5dee3` (peeled v30.0), with original copyright and MIT COPYING. All six retained source/license files are inert; no downloaded C++ is compiled or executed.

The fixture uses the complete490-byte mainnet block170: one134-byte coinbase and one275-byte transaction. The raw header, both full transactions, both raw txids and complete two-leaf Merkle root are independently recovered from the original block, with the raw header digest checked against its explorer/display block hash. Compact-block, request and response packets are **derived protocol fixtures around this actual block**, not historical network captures from2009. The existing immutable SPV packet retains the original block source metadata.

The native kernel computes single-SHA256 of `header80 || nonce_le64`, interprets the first16 bytes as two little-endian SipHash keys, hashes the actual raw transaction to its raw32-byte SHA256d ID, and checks the low48 bits of SipHash2-4. A6-byte decoded shortID must be below2^48. The prefilled transaction must occupy differential index0. In the requested path, the request and response blockhashes both equal native SHA256d of the actual header, and the single missing differential index is1. In either path, both actual transaction IDs must differ and their complete ordered Merkle root must equal the raw root in the header.

One structured witness enters once: `(nonce64, shortID64, prefilledIndex8, coinbaseBuffer255, fill)`, where fill is either one actual mempool transaction buffer511 or the actual `(requestHash, missingIndex, responseHash, responseTransactionBuffer511)` record. The first stage hashes the coinbase and drops its raw buffer; the fill stage hashes the actual selected transaction once and drops its raw buffer. Both shortID and Merkle checks use projections of the same resulting txid. The kernel contains zero Witness nodes, and the prepared driver confirms eligibility and exact type/kernel/canonical composition CMR per vector.

This is a **client** reconstructor under an authenticated80-byte header and canonical decoded transport schema. Header-chain/PoW/finality authentication and normal transaction/UTXO/consensus validation after reconstruction are external tasks; reconstruction is not proof of a valid block or payment. Version/connection negotiation and canonical P2P transport decoding are client boundaries. The native environment is unused; transaction-budget comparisons do not imply an onchain spend.

The exact bound is two **legacy** transactions, one prefilled coinbase at0, one shortID and one candidate or requested transaction at1. Legacy txid=wtxid means the same calculation supports BIP152v1 and this legacy subset ofv2; general witness transactions/witness commitments are not claimed. Arbitrary preforward positions/counts, larger mempools, ambiguous shortIDs and collision search/fallback are outside this bound. Such failures call for full-block fallback and are not a reason to penalize a peer.

`Ref.CompactBlock` provides full standard-wire encoders and strict decoders for the bounded cmpctblock/request/response, including minimal CompactSize counts and exact transaction serialization roundtrips through the canonical raw-opHash base serializer. Its reference checks all actual hashes, both complete fills and exact packets. It also reproduces all three published Core request index/boundary examples: `[0,1,3,4]`, maximum65535, and the original overflow deltas `[0x7000,0x8ffe,0]`. Nonminimal CompactSize and wrong count cases reject in the codec. Those counts are outside the native sum schema, so codec rejection is not falsely counted as native execution.

| Pinned official Core procedure | Exact native coverage / gap |
| --- | --- |
|SimpleRoundTripTest|Derived two-transaction analogue for mempool/missing-fill behavior; original randomized three-transaction block is outside this native bound.|
|NonCoinbasePreforwardRTTest|Non-coinbase preforward position excluded.|
|SufficientPreforwardRTTest|Multiple prefilled transactions excluded.|
|EmptyBlockRoundTripTest|Single-transaction/no-shortID profile excluded.|
|ReceiveWithExtraTransactions|Extra-cache/collision search excluded.|
|TransactionsRequestSerializationTest|Complete published index example reproduced by independent reference.|
|TransactionsRequestDeserializationMaxTest|Complete65535 bound reproduced by independent reference.|
|TransactionsRequestDeserializationOverflowTest|Complete original overflow-delta rejection reproduced by independent reference.|

All eight source procedures are inventoried in `core-bip152-test-inventory.tsv`, with source lines and verdicts. They are C++ procedures, not a published static block/shortID JSON set. No claim is made to run their randomized blocks or Bitcoin Core itself. The complete reference has12 passing checks, recorded in `data/compact-block-reference-rts.txt`. An earlier local reference guard incorrectly expected an empty witness-vector list for legacy inputs instead of one empty stack per input; that local diagnostic failure is retained separately and corrected without upstream changes.

| Complete native vector | Expected / actual |
| --- | --- |
| Actual complete missing getblocktxn/blocktxn fill | Accept / Accept |
| Actual complete one-candidate mempool fill | Accept / Accept |
| Fresh nonce with exact recomputed shortID | Accept / Accept |
| Nonce changed without corresponding shortID | Reject / Reject |
| Noncanonical high16 bits in decoded shortID | Reject / Reject |
| Wrong prefilled differential index | Reject / Reject |
| Actual coinbase raw bytes changed | Reject / Reject |
| Actual returned transaction raw bytes changed | Reject / Reject |
| Wrong request raw blockhash | Reject / Reject |
| Wrong response raw blockhash | Reject / Reject |
| Wrong missing differential index | Reject / Reject |
| Wrong actual mempool candidate bytes | Reject / Reject |
| Duplicate actual transaction IDs | Reject / Reject |

All13 prepared native results and13 additional direct functional results pass with CMR `a642897c525bf7a0e9a4472051d186aff0aa142f48b7bb612e36f807a06580a7`. GHC9.8.4 `-O1`, `-N1 -M3G -s`:100.458 seconds elapsed,1,351,863,352 maximum live bytes and2809MiB total RTS memory. Exact source/object/driver snapshots, executable/log and packet hashes are in `data/compact-block-provenance.json` and `compact-block-freeze/`. This is standalone validation, not a full-corpus cost measurement.

Reproduce with `tools/extract_bip152_vectors.py`, `CompactBlockReference.hs` and `CompactBlockSmoke.hs`. Compile the smoke with the cached package database and `-ireports/data/compact-block-freeze/src`, using its frozen driver, then run `+RTS -N1 -M3G -s`. `python3 tools/check_bitcoin_growth5_packet.py` verifies all6 primary and4 derived files, cross-packet source hashes and LF TSVs offline. No shared registry/Cabal/test edits are made by these tools.
