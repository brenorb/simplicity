# Candidate: `bip341_hashes` — BIP 341 precomputed transaction hashes

## Type signature
`bip341_sha_outputs`, `bip341_sha_sequences`, `bip341_sha_prevouts`, `bip341_sha_amounts`, `bip341_sha_scriptpubkeys`: `1 -> Word256`; `bip341_current_sha_annex`: `1 -> S Word256`; for BIP 119, `bip119_sha_scriptsigs`: `1 -> S Word256` (none when every scriptSig is empty)

## Specification
Each is the corresponding BIP 341 (or BIP 119) hash of the transaction, as Bitcoin Core's `PrecomputedTransactionData` already computes it. The definitions need raw output scripts and scriptSigs, which no Bitcoin Simplicity primitive exposes, so there is no Simplicity reference expression. The closest executable references are the witness-checked re-serializations in `src/JetDiscovery/Lib/TxSer.hs` (`shaOutputs`, `shaSequences`) and `Corpus/Bip446TemplateHash.hs`, which pass the upstream BIP 119 and BIP 446 vectors.

## Cost (ESTIMATE)
ESTIMATE: priced like the existing precomputed transaction-hash jets (`outputs_hash` = 0.059 WU, `input_sequences_hash`, `input_script_sigs_hash`): the value is computed once per transaction and read by the jet. What-if costs come from cost-only stand-in variants (`src/JetDiscovery/Candidates/Variants.hs`).

## Generality
Primitive. One family serves BIP 119 CTV, BIP 446 TEMPLATEHASH, BIP 448 (LN-Symmetry), BIP 346 TXHASH, BIP 118 APO-exact digests and any BIP 341-compatible signature hash computed in Simplicity.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low to medium. The closest proven jets are the Bitcoin transaction-hash and totals jets on the totals branch (`outputs_hash`-style hashing over the txEnv, with the reusable SHA-256 streaming lemmas). The new work is computing BIP 341 serializations in `C/bitcoin/txEnv.c` and proving them against a Haskell specification over raw scripts; the C side needs the raw scripts in the txEnv, which Bitcoin Core has.

## Alternatives considered
(a) A raw-bytes primitive (`output_script(i)` returning bytes). This breaks Simplicity's design of bounded, typed values: script lengths are unbounded. (b) Re-serializing from witness bytes, as the corpus does today: correct, but 50-100x more expensive in the static bound, because every buffer slot is priced at its maximum size. (c) Simplicity-native template hashes (`bip119-ctv-native`): cheap and as strong, but not hash-compatible with the BIPs.

## Corpus evidence
<!-- EVIDENCE -->
