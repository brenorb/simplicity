# Complete published mixed-script PSBT finalizer and extractor

`app-bip174-mixed-psbt-finalizer-extractor` is a bounded **CLIENT MODE** verifier
for the complete published two-input/two-output workflow. It covers the legacy
P2SH 2-of-2 input and the nested P2SH-P2WSH 2-of-2 input together. This is one
application group. It does not execute as a Bitcoin spend of either script.
All23 actual vectors pass under canonical CMR
`6be88a45f1aa2e60ba2b2ea734e7d3c383bdee92e5f5335b8d92c75d66e19ec9`.

The primary sources are pinned
[BIP174](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0174.mediawiki),
[BIP370](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0370.mediawiki)
and [BIP143](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0143.mediawiki).
The first two are BSD-2-Clause; BIP143 explicitly states public domain. Complete
inert copies and their retrieval metadata are retained in Growth2/Growth3.
Growth9 hashes those unchanged sources and contains the complete local inventory.
No downloaded code is executed or linked.

| Complete source inventory | Invalid syntax/version | Valid syntax | Role-negative | Workflow | Locktime | Total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| BIP174 | 20 | 10 | 4 | 14 | 0 | 48 |
| BIP370 | 24 | 14 | 0 | 0 | 10 | 48 |

Every inline binary record, exact source line, hex, hash, expected role, wire
map shape and native scope verdict is in `psbt-all-inline-vectors.tsv`. All95
provided Base64 counterparts decode to the same bytes. The lone hex-only item
is the published extracted network transaction. The independent byte model
reproduces all ten BIP370 locktime outcomes, including the incompatible pair.
The inventory reader checks CompactSize, duplicate keys, map framing and
version/count shape. Its structural results are **not** full PSBT validation;
some source-invalid type/sighash/role combinations pass framing. Only BIP174
workflow records40,41,42 exercise this exact native profile. The other93 records
remain inventoried source evidence, with no native pass or count credit.

The independent reference parses the actual fully signed source PSBT (1332B),
checks the actual legacy prevtx txid, both UTXO scripts and the nested witness
script hash, and verifies all four real DER/ALL signatures. It clears obsolete
input data while retaining the UTXOs, fills `0x07`/`0x08`, and produces exactly
the published finalized PSBT (976B) and extracted transaction (628B). It
checks both real Bitcoin primitive views for raw outpoints, UTXO and final
scriptSig hashes, and actual output values/scripts. The source transaction and
the fresh signed reference fixture both round-trip the no-witness base writer
and full witness parser. Published fixture private keys are used only to sign
the alternate test case. It moves the valid high-R DER padding from the legacy
signature to the SegWit witness, exercising both variable length computations.

| Exact published digest | Raw bytes, hex |
| --- | --- |
| Legacy ALL digest (input0) | `ff089a1634a922b1dc623aca50b2b922c1487786bae4476ab1ade9897ea65d5f` |
| BIP143 ALL digest (input1) | `c5a3684b155f6f441ae3fad632a3463a6d5a00c0f0e84075f5649847c17b2b3b` |
| Partial PSBT, single SHA256 | `469d26cf0652d6ffaddd33a7395ab3498d8694ed9ed15b4dbb96255927ff5391` |
| Final PSBT, single SHA256 | `e405299f0b4b0e835bd3f128c978378d1623940a983debf606a8a1bd09e6636f` |
| Final txid, SHA256d without witness | `cd66f9df46cc6e34f5e3775d8aa2f19e2e0d699423076023439c312bf1df01c0` |
| Final wtxid, SHA256d with witness | `9cb369c45cf33aa8fc5081cdd0a2a3c9fb785b1ffbd9e30c89cc73f036687391` |

The native program takes one structured 3072-bit witness containing four
logical compact ECDSA signatures and four separately checked result digests.
It recomputes the legacy ALL digest and BIP143 ALL digest, including the actual
BIP143 prevouts, sequences and outputs subhashes over the fixed authenticated
session fields. It checks all four ECDSA equations and the canonical DER
profile: positive 32-byte magnitudes, optional required zero pad for high R,
low S, and ALL01. The same actual signatures feed the complete partial and
final PSBT maps, both finalized input scripts, the exact witness stack, and
the no-witness/full network serializations. CompactSize lengths of the changed
map fields, script pushes and stack elements are computed inside Simplicity.
Only explicit projections reuse witness values. The ECDSA term itself is shared
locally and contains no witness.

The actual finalized primitive view must have current input0, two inputs and
two outputs. It binds both raw previous hashes/indices, input values, UTXO
scripts, sequences, both finalized scriptSig hashes, version/locktime and both
output amounts/scripts. The primitive view does not expose the SegWit stack;
the separately supplied full network wire digest is checked as wtxid. Client
transport parsing, session authentication, actual UTXO existence, consensus
validation and broadcast remain outside this statement. The compiled session
contains the complete published unsigned transaction and the retained map
metadata; it does not claim a general v0/v2 parser, arbitrary sighash modes,
arbitrary DER lengths, witness programs or script execution.

Reference checks are recorded in `reports/data/psbt-reference-final-rts.txt`:
exit0,0.520s elapsed, maximum residency3,233,016B. Reproduce source extraction
with `python3 tools/extract_psbt_vectors.py` and offline checking with
`python3 tools/check_bitcoin_growth9_packet.py`. Compile the local
`tools/PsbtReference.hs` and `tools/PsbtSmoke.hs` with GHC9.8.4 `-isrc` and the
cached `dist-newstyle/packagedb/ghc-9.8.4` `jet-discovery` package.

The23 actual vectors comprise two complete positives and21 same-CMR negatives.
All four changed-signature cases regenerate matching complete serialization,
digest claims and actual scriptSigs, isolating signature verification. A high-S
alias also rejects. Four separate digest corruptions and12 altered actual
environment cases reject, including either finalized scriptSig, reversed raw
outpoint bytes, UTXO script/value, payout, sequence, locktime, version, current
input and output count. Both positives and every negative use the same actual
typed prepared kernel with per-vector canonical whole-program CMR checks.

`reports/data/psbt-full23-3g-rts.txt` records23/23PASS, exit0,156.053s RTS elapsed,
2,407,531,464B maximum residency and3148MiB total RTS memory at
`-N1 -A16m -M3G -s`. This is complete execution evidence, not a measured WU
or Bitcoin budget claim. The accompanying provenance hashes the executable,
log and exact source/input closure, unchanged during the run. `tools/run_psbt_vectors.py`
reproduces the bounded run from the independently compiled local `PsbtSmoke`
binary. Registration and the shared whole-corpus measurement are separate.
