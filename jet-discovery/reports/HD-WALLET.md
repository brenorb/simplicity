# Native BIP32 public-HD withdrawal wallet

`app-bip32-public-hd-withdrawal` is a complete native Bitcoin spend condition: derive a nonhardened child from a configured public HD root, require that child's signature on the actual transaction, and pay its actual Taproot beneficiary while preserving all collateral minus1000 satoshis. All11 full prepared vectors with exact per-vector CMR checks and all9 actual source/digest-boundary checks pass. It earns one application group; child indices, source roots, address variants and the HMAC helper earn no extra group.

The primary sources are [BIP32](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0032.mediawiki), BSD-2-Clause, and [BIP341](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0341.mediawiki) for the standard empty-tree TapTweak output. Source texts and licenses remain in the frozen source packets. `Lib.HmacSha512.hmac37` computes actual RFC2104 HMAC-SHA512 for a32-byte chaincode and37-byte `compressed_parent_public_key || BEchildIndex`, using four SHA512 compressions. No digest/midstate is witnessed. Its parent's separate20 stdlib-derived cases plus5 corruptions passed before this wallet uses it; it is a component, not another application group.

The root xpub is a committed wallet parameter. The kernel checks index<2^31, compressed prefix2/3, canonical parent x and actual decompression, then computes the full HMAC digest. `IL>=n` or an infinite resulting child reject. `IL=0` is **valid CKDpub** when its resulting point is not infinity; rejecting it unconditionally would disagree with BIP32. The child point is the actual parent point plus IL*G; the returned chaincode is computed and independently checked in the source tests, then discarded by this one-level withdrawal policy.

A single `(index32, BIP340_signature512)` witness enters once. The same projected child point feeds its actual native `sig_all_hash` authorization and the actual output. The payout uses `lift_x(child_x) + taggedHash_TapTweak(child_x)*G`, with tweak range/infinity checks and correct even-y normalization. Its exact canonical P2TR script hash must match output0. The input amount equals checked `output_amount+1000`, and the output must be positive. There is exactly one current input0 and one output, version2, locktime0, sequenceFFFFFFFE, empty scriptSig and no annex.

The actual funding input must have the standard unknown-log NUMS internal key, no sibling leaf, and the P2TR script computed from that internal key and this program's actual TapLeaf hash. The fixtures use the base Bitcoin library's actual funding-script derivation, rather than a fake direct CMR output. An independently focused source audit by the contract agent found no native layout/funding mismatch; it confirmed that both signature and payout use the same child and that indexed input0 is the actual spend. This audit supplements the runtime checks and is not a formal security proof.

This wallet is one ownership domain. An xpub plus one nonhardened child **private** key exposes its parent private key, as BIP32 explains; it is not a key-isolated delegation scheme. Ordinary signatures do not reveal that private key. Master seed/hardened account setup, canonical Base58Check xpub decoding, backup and address-index management remain authenticated wallet setup. A rolling-child continuation would be an extension of this same wallet family, not a second group.

| Complete pinned BIP32 source coverage | Reference / native evidence |
| --- | --- |
|All5 test sections|All inventoried, including leading-zero and invalid-extended-key sections.|
|17 valid public/private extended-key pairs,34 keys|All Base58Check/structure-valid; all17 exact full compressed pub/private point relations independently checked.|
|16 invalid extended keys|All rejected by the independent setup decoder: version/prefix, root metadata, scalar, curve and checksum cases. These are setup decoding tests, not claimed native transaction vectors.|
|4 master seeds|All exact master secrets/chaincodes reconstructed by Python stdlib HMAC-SHA512. Master generation is external setup, not falsely claimed native32-byte-key HMAC.|
|13 private CKD edges|All exact child private keys, chaincodes, indices, depths and parent fingerprints reconstructed by stdlib HMAC.|
|All6 nonhardened public CKD edges|Independent curve/chain reference and actual Simplicity full HMAC+point+chain results pass for every row.|
|Post-digest boundary IL0, IL=n, and IL=n-parentSecret|Actual Simplicity checks accept unchanged parent for0, reject n, and reject infinity. These are explicit component stress cases, not claims that a real random HMAC output equaled these rare values.|

`bip32-all-valid.tsv`, `bip32-all-invalid.tsv`, `bip32-all-ckd-edges.tsv` and `bip32-public-ckd-vectors.tsv` retain every row; none is silently sampled. The native transaction fixture uses the published vector2 master/child0. Index1 and2^31-1 are documented derived cases. A derived public formula at index2^31 produces a genuine corresponding child/signature solely to isolate rejection of the forbidden hardened public index; it is not labeled valid BIP32 CKDpub.

| Complete actual native vector | Expected / actual |
| --- | --- |
|Published source child0 withdrawal | Accept / Accept |
|Derived child1 withdrawal | Accept / Accept |
|Maximum nonhardened index2^31-1 | Accept / Accept |
|Genuine signature for forbidden hardened public formula | Reject / Reject |
|Fresh child signature for diverted beneficiary | Reject / Reject |
|Fresh child signature with wrong exact fee | Reject / Reject |
|Child signature does not match the chosen index | Reject / Reject |
|Fresh signature with changed committed lock policy | Reject / Reject |
|Fresh signature but wrong actual funding script | Reject / Reject |
|Fresh signature but substituted known-log internal key | Reject / Reject |
|Noncanonical final child signature scalar n | Reject / Reject |

The full run passes all9 native source/boundary checks and all11 prepared transaction vectors with CMR `13b7b854c3618be0efecc3b01d8d85366b73f828504dc45cf94c1578a63d97f0`. At GHC9.8.4 `-O1`, `-N1 -M16G -s`:251.016 seconds elapsed,5,837,630,296 maximum live bytes and12950MiB total RTS memory. Exact source/object/driver snapshots, binary/log hashes and input packet hashes are in `data/hd-wallet-full16g-provenance.json` and `hd-wallet-full16g-freeze/`. The3G-capped core attempt exhausted its heap before the first CKD result; its14.789-second log and exact source snapshot are preserved as a failed capacity check, not mathematical or successful-vector evidence. These are Haskell construction/evaluation resources, not C interpreter memory requirements or a measured Bitcoin WU result.

`HdWalletWire.hs` independently reconstructs the positive fixture from the **logged measured CMR**, verifies its actual child signature and final payout private/public relation, and checks exact base wire/every raw outpoint roundtrip. The real funding script is `51208b58fd3dbcadcef99a070cb0e6b339f66ec10d7f750377fba0e86aa83ff8f020`; the child0 payout is `51202ec13c43c90b6f7e345a37739fdd3f7f3b6d9ac4ae8650cdd581650927167577`. `hd-wallet-measured-wire.tsv` retains the actual sig_all_hash,64-byte child signature and unsigned base transaction. It is a synthetic funding UTXO/typed environment fixture, not evidence of live coins or a broadcast/network-accepted Simplicity transaction. Full-corpus WU/program-size feasibility remains the root-owned analysis step.

Reproduce source extraction with `tools/extract_bip32_vectors.py` and references with `HdWalletReference.hs`/`HdWalletWire.hs`. Compile the frozen `HdWalletSmoke.hs` with the cached GHC9.8.4 package DB and `-ireports/data/hd-wallet-full16g-freeze/src`; run `all +RTS -N1 -M16G -s`. The executable runs source/boundary checks first and aborts on failure before the full wallet. `python3 tools/check_bitcoin_growth6_packet.py` verifies the complete pinned source hash, all6 local derived artifacts and LF TSVs. No upstream source/consensus jet/cost is edited, and the new wallet does not change any existing program's semantics or CMR.
