# Bitcoin application growth: later batch

The two independently validated entries below are registered through `Corpus.BitcoinGrowth2`. The first three applications and their signed milestone remain described by the frozen `BITCOIN-GROWTH.md`. Each row below is one complete bounded deployment predicate; cryptographic helpers, parameter variants and source-vector counts do not create additional application groups. Standalone execution below is not a fresh full-corpus cost result.

## Mixed-input silent-payment output condition

`app-silent-payment-output-covenant` implements a bounded [BIP352](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0352.mediawiki) sender output condition with the exact [BIP374 v0.3.1](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0374.mediawiki) ECDH proof. Source is `Lib.SilentPayment`, with independent byte/Integer reference in `Ref.SilentPayment`. The structured proof occurs at one `witness` node; every later use is a projection of that actual input.

The supported transaction has exactly two eligible inputs and one output. Input0 is the current P2TR scriptpath input; its actual internal key must differ from the BIP341 NUMS point. Its actual funding script is computed from that internal key and this program's TapLeaf CMR. Input1 is compressed P2PKH: real HASH160 binds its key to the actual spent script, and SHA256 of the exact two-push scriptSig binds the extracted key and DER signature bytes to actual `InputScriptSigHash`. The fixture generates a genuine low-S legacy ECDSA signature for the actual transaction. Bitcoin consensus remains responsible for that legacy signature and the current Taproot control block. Other-input Taproot witness metadata is unavailable to the program, so other-P2TR, P2WPKH and P2SH-P2WPKH inputs are outside this bound.

The program adds the authenticated eligible keys, chooses the smallest **serialized wire outpoint** lexicographically (including the little-endian index), applies the exact BIP352 input and shared-secret tagged hashes with required scalar rejection, and derives the committed recipient's k=0 P2TR output. The weighted ECDH point is proved through BIP374's compressed `(A,B,C,G,R1,R2)` transcript, with the optional message equal to the actual native `sig_all_hash`. Both challenge and response must be canonical scalars; public points must be canonical and on curve. No sender secret is witnessed. Output value must equal both inputs minus1000 satoshis.

This is the chosen Simplicity leaf or signer/output-validation condition. It is **not an inescapable Taproot covenant**: a BIP352 sender knows the current output private key and can elect a keypath spend. The example is not a collaborative transaction protocol with hidden-key security claims. It supports one committed recipient, no labels, no group sweeps and k=0.

All29 upstream JSON groups were inventoried as59 sender/receiver role cases in `bip352-vector-inventory.tsv`. All three compatible sender derivation cores (groups8,9,23) match the upstream weighted shared point and output key in both the independent reference and actual Simplicity. The remaining56 role cases are outside the complete supported bound; their exclusion is recorded rather than represented as native transaction coverage. The complete native proof and script provenance vectors are derived fixtures, not upstream BIP352 transactions.

| Complete native vector | Expected / actual | Exact per-vector CMR |
| --- | --- | --- |
| Authenticated mixed input keys, valid native-message BIP374 proof, correct payout | Accept / Accept | Same |
| Same txid, indices1/256: wire-index byte ordering | Accept / Accept | Same |
| Fresh valid BIP374 and legacy signatures for a diverted payout | Reject / Reject | Same |
| Fresh valid signatures/proof with changed conservation fee | Reject / Reject | Same |
| Noncanonical challenge e=n | Reject / Reject | Same |
| Noncanonical response s=n | Reject / Reject | Same |
| Shared point changed at its single actual proof occurrence | Reject / Reject | Same |
| Witness DER bytes disagree with actual input1 scriptSig | Reject / Reject | Same |
| Wrong extracted current P2TR output key | Reject / Reject | Same |

All9 actual jetted Haskell Simplicity evaluations pass with CMR `7ac619277ae12417468d7f39e1b51f7a085a2a9a3e79d43deb35377997fc3608`. At GHC9.8.4 `-O1`, `-N1 -M3G -s`, elapsed time1396.691 seconds, max live2,303,498,176 bytes, total RTS memory3128MiB. Log `data/bitcoin-growth2-silent-payment-rts.txt` and `data/bitcoin-growth2-silent-payment-provenance.json` preserve exact three-module standalone source snapshots, hashes and the nine same-CMR outcomes. Separate core/reference logs are `silent-payment-core-rts.txt` and `silent-payment-reference-rts.txt`; the core check took24.738 seconds and tested all3 supported upstream cases plus BIP374 transcript/canonical-scalar negatives. These are not Bitcoin Core/C interpreter network-transaction validations.

## BIP127 reserve ownership and exact sum

`app-reserve-ownership-and-sum` is a bounded **client-mode** [BIP127 v1.0](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0127.mediawiki) proof verifier. The proof transaction deliberately has a nonexistent commitment input and cannot be broadcast. It is neither a redeemable escrow nor proof of solvency. The client must populate the primitive environment from the actual virtual transaction and an externally authenticated, block-specific UTXO view; the program does not independently establish chain membership or unspentness.

The bound is exactly three inputs: zero-valued OP_TRUE phantom metadata followed by two P2TR keypath reserve inputs, with empty scriptSigs, no annex, all sequencesFFFFFFFF, version2 and locktime0. One OP_RETURN output equals the exact, positive, bounded reserve sum; all three outpoints must differ. Both reserve keys bind their actual UTXO scripts. Both actual BIP341 ALL01 messages are constructed from all real outpoints, amounts, serialized scripts, sequences, output and the respective input index; BIP340 checks both signatures. A single structured `(raw_message, two_keys_and_signatures)` witness feeds the zero-Witness `Assert+Primitive` `reserveKernel` through projections.

The commitment follows normative **single SHA256** of `Proof-of-Reserves: ` plus the UTF-8 message. Pinned BDK `bdk-reserves` currently computes SHA256d; the exact revision, inert source and concrete incompatible bytes are documented separately in `BIP127-MISMATCH.md`. No upstream code is executed or corrected. The supported public challenge is `Some Message`, with a <=511-byte raw-message bound. Base64/PSBT/transport decoding is a client boundary; a canonical full proof serializer roundtrips actual three-input witness data through the local transaction parser.

The pinned BIP127 specification publishes no official proof transaction vector set. For the signature reference, **all seven** official BIP341 keypath signing cases are inventoried in `bitcoin-growth2/bip341-signing-inventory.tsv`; the sole ALL01/no-annex case is compatible with the byte-oriented reference. Its exact digest and upstream signature both pass. The other six signing modes are explicitly outside this reference, and the separate scriptPubKey vectors are not claimed as reserve proof vectors. The derived complete proof is retained as `bip127-derived-proof.hex` and `.tsv`; `reserve-proof-reference-rts.txt` records the single-SHA commitment, both independently indexed signatures, exact sum and canonical wire checks.

| Complete client proof vector | Expected / actual | Exact per-vector CMR |
| --- | --- | --- |
| Two independently indexed ownership signatures and exact reserve sum | Accept / Accept | Same |
| Same actual reserve outpoint duplicated, fresh valid signatures | Reject / Reject | Same |
| BDK double-SHA commitment, fresh valid signatures | Reject / Reject | Same |
| Nonzero virtual fee, fresh valid signatures | Reject / Reject | Same |
| Nonempty P2TR input scriptSig, fresh valid signatures | Reject / Reject | Same |
| Reserve signature slots exchanged | Reject / Reject | Same |
| Different audit message reuses old signatures | Reject / Reject | Same |

All7 actual jetted Haskell Simplicity evaluations pass with CMR `dcdf2a0b66e03c9c12db442bb6684bd5226692cf39469dd18e884c9ed7f9cd8c`. At `-N1 -M3G -s`, elapsed342.617 seconds, max live1,097,463,240 bytes and total RTS memory2453MiB. Exact three-module source snapshots, log hashes and outcomes are in `data/bitcoin-growth2-reserve-provenance.json` and `data/bitcoin-growth2-reserve-rts.txt`. This standalone result establishes the bounded client's transaction/signature predicate; it is not an onchain spending result or a fresh full-corpus cost measurement.

## Remaining source gates

After adoption of the safe prepared-kernel API, a fresh combined run passed **all16 SilentPayment+ReserveProof vectors**. Both kernels were eligible, and both complete canonical CMRs exactly matched their earlier ordinary whole-program runs. Each vector still receives a type, kernel fingerprint and canonical composition-CMR check in `runVectors`; preparation is an execution optimization, not permission to reuse a result from a changed kernel. The fresh run took261.205 seconds at `-N1 -M3G`, max live2,156,388,592 bytes and total RTS memory3126MiB. `data/bitcoin-growth2-prepared-provenance.json` retains the exact typed-kernel, runner and driver source copies, executable hash and log hash. No compiled DAG is held globally by these entries. The integrated shared executable subsequently passed all9 silent-payment vectors in178.917 seconds and all7 reserve-proof vectors in64.650 seconds, each explicitly using prepared evaluation. The frozen-executable launch manifests and observed exit0 records are `data/bitcoin-growth2-shared-silent.json` and `data/bitcoin-growth2-shared-reserve.json`; the corresponding `.txt` files contain every result. The small difference from the earlier runner snapshot is prepared-path note observability, not program semantics.

| Scope | Remaining gate | Credit |
| --- | --- | --- |
| Offered HTLC | Full BOLT3 branch/signature/template coverage; share received-HTLC group if differences are direction/branch constants. | No extra group from a mirrored policy. |
| Ark round refresh | Actual funded VTXO/connector/forfeit relationships and ownership, not a generic Merkle-root balance transition. Primary HTML available; paper endpoint403 remains a gap. | Unimplemented. |
| Numeric DLC adaptor CET | Exact oracle digit transcript, summed signature points/scalars, actual ECDSA adaptor DLEQ and decryption, standard CET encoding/digest and actual payouts. Source review/reference work underway. | Unimplemented. |
| BOLT12 invoice authorization | Full sorted TLV/nonce Merkle transcript, mandatory invoice/path fields and copied request, real amount/node/payment-hash checks and authenticated acceptance-time expiry. nLockTime is not a current wall clock. | Unimplemented. |
| Utreexo / Garrison / Payment Trees / Sleepy / Elmo / Thora / Daric | Full primary texts and materially distinct complete predicates, beyond search metadata/abstracts. | No implementation inferred. |

## Reproduction and provenance

The immutable BIP/DLC/BOLT source packet is `vendor-specs/bitcoin-growth/manifest.json`; supplementary source archives, BIP341 specification/vectors and license/hash metadata are `vendor-specs/bitcoin-growth2/manifest.json`. Downloaded Rust/other source is inert `.txt` or archives. Local extraction is reproducible with `tools/extract_bip352_growth_vectors.py` and `tools/extract_bip341_reserve_vectors.py`, both producing LF TSV files from retained JSON without executing upstream code.

Standalone tools `BitcoinGrowth2Smoke.hs`, `SilentPaymentReference.hs`, `SilentPaymentCore.hs` and `ReserveProofReference.hs` compile against the cached GHC9.8.4 package database, with these unregistered modules supplied via isolated `-i` source overrides. The complete smoke checks every vector's actual CMR before evaluation; fresh malicious transactions are signed/proved where required. Shared registry integration is complete; current shared-run vector evidence, source fingerprint freeze and fresh cost measurement remain separate root-owned steps.
