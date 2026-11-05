# Script-extension BIP and proposal inventory

Snapshot date: **2026-11-04**. Target: `bitcoin/bips` at immutable commit
[`a0c977f3755da6476b955677ca9318334a2432c4`](https://github.com/bitcoin/bips/tree/a0c977f3755da6476b955677ca9318334a2432c4).
The complete index has **220 numbered rows**, including three unlinked allocated numbers;
**51** rows have layer `Consensus (soft fork)`. All 51 are recorded in
[`softfork-triage.tsv`](../vendor-specs/bip-inventory/softfork-triage.tsv), and all 220
rows in [`index-all.tsv`](../vendor-specs/bip-inventory/index-all.tsv).

“Open” here means **not Closed or Deployed** at this revision. The index currently uses
Draft, Complete, Closed and Deployed for softfork rows. This deliberately includes
Complete specifications that have not been deployed: **24 nonterminal softfork rows**.
The table below inspects all 24, not a selection. There are **16 in-scope computation
proposals**; eight rows are excluded or adjacent with an explicit reason. Inclusion
means a useful computation demand signal, not complete Script consensus compatibility.
BIP 345 OP_VAULT is now **Closed** and is retained as historical corpus material, not
counted as an open proposal. BIP 347 OP_CAT is **Complete**, not Draft.

All 24 specifications and every `.json`, `.csv`, `.txt`, `.hex`, `.md` and `.mediawiki`
data asset under their upstream directories are vendored (46 files). The complete
GitHub tree was checked for truncation. Source URLs, Git blob hashes, complete SHA-256
hashes, byte counts and per-BIP licenses are in
[`manifest.json`](../vendor-specs/bip-inventory/manifest.json). Diagrams and source code
were not downloaded by this audit; embedded spec vectors remain in each complete text.
Do not compile or execute downloaded material.

Reproduce from `jet-discovery/`:

```sh
python3 tools/fetch_bip_inventory.py          # fetch the immutable snapshot and audit blobs
python3 tools/fetch_bip_inventory.py --offline
python3 tools/fetch_proposal_sources.py --offline
python3 tools/extract_bip360_vectors.py
```

## Every open softfork row

The program IDs below link logically to the generated [corpus index](../corpus/README.md)
and [measured cost table](corpus-results.md). Costs come from that runner, whose declared
bounds and assumptions apply; this inventory does not assign fabricated costs to
unimplemented modes. A “gap” is unimplemented scope, not evidence that a new jet is
necessary. No new consensus primitive or jet is registered here.

| BIP | title | status | in scope? | implementation / exact gap |
| --- | --- | --- | --- | --- |
| [18](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0018.mediawiki) | hashScriptCheck | Complete | historical | Hashing and delegation are expressible, but this is an historical P2SH precursor; no new jet-demand application. Complete in index does not imply deployed. |
| [53](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0053.mediawiki) | Disallow 64-byte transactions | Draft | consensus-policy | Minimum serialized transaction length; no new Script computation. |
| [54](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0054.md) | Consensus Cleanup | Complete | consensus-accounting | Consensus cleanup (timewarp, coinbase, size and legacy sigop limits); accounting rules are not application kernels. |
| [98](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0098.mediawiki) | Fast Merkle Trees | Draft | yes | Fast-SHA256 is measured by bip116-merklebranchverify; standalone hash primitive already expressible with SHA256 block jet. |
| [116](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0116.mediawiki) | MERKLEBRANCHVERIFY | Draft | yes | bip116-merklebranchverify implements bounded single-leaf paths; arbitrary multi-leaf proof grammar not implemented. |
| [117](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0117.mediawiki) | Tail Call Execution Semantics | Draft | yes | bip117-tail-call models witness-program delegation with disconnect; not a byte-for-byte Script tail-call interpreter. |
| [118](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0118.mediawiki) | SIGHASH_ANYPREVOUT for Taproot Scripts | Draft | yes | bip118-apo has rebindable semantics and a Simplicity-native digest; exact BIP341/BIP118 wire hash remains a compatibility gap. |
| [119](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0119.mediawiki) | CHECKTEMPLATEVERIFY | Draft | yes | bip119-ctv-exact reconstructs the exact template digest; all 193 in-range upstream transaction/index pairs are now loaded; 207 impossible current indices are outside Bitcoin PrimEnv. |
| [300](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0300.mediawiki) | Hashrate Escrows (Consensus layer) | Draft | global-state | Hashrate escrow requires sidechain/withdrawal-voting consensus state, not available to a Bitcoin input expression. |
| [301](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0301.mediawiki) | Blind Merged Mining (Consensus layer) | Draft | mining | Blind merged mining changes coinbase/miner commitments, not Script applications. |
| [346](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0346.md) | OP_TXHASH | Draft | yes | bip346-txhash executes all 150 upstream hash vectors; Haskell selector decoding is not on-chain; tapscript-context witness values are not authenticated by Bitcoin Simplicity. |
| [347](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0347.mediawiki) | OP_CAT in Tapscript | Complete | yes | [bip347-op-cat](BIP347-OP-CAT.md) checks exact byte concatenation, including empty operands and the complete 520-byte result bound, with one typed witness. Script activation, policy, stack underflow and surrounding opcodes are outside the component. |
| [348](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0348.md) | CHECKSIGFROMSTACK | Draft | yes | bip348-csfs and bip348-csfs-32; 32-byte message verification already has a jet; variable-length hashing measured separately. |
| [349](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0349.md) | OP_INTERNALKEY | Draft | yes | bip349-internalkey uses the existing internal-key primitive and Schnorr verification jet. |
| [360](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0360.mediawiki) | Pay-to-Merkle-Root (P2MR) | Draft | yes | bip360-p2mr-output models a Simplicity leaf; bip360-upstream-p2mr-output validates every published successful arbitrary-leaf output construction. P2MR consensus activation and leaf execution are not emulated. |
| [361](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0361.mediawiki) | Post Quantum Migration and Legacy Signature Sunset | Draft | migration | Informational migration and legacy-signature sunset schedule, not a verification algorithm. PQ schemes are separate corpus demand signals. |
| [440](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0440.mediawiki) | Varops Budget For Script Runtime Constraint | Draft | runtime-accounting | Varops budgeting changes Script runtime accounting; does not add an application computation. Do not transfer its budget model into Simplicity. |
| [441](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0441.mediawiki) | Restoration of disabled script (Tapleaf 0xC2) | Draft | yes | bip441-bignum-modmul measures a 256-bit restored-arithmetic kernel; unbounded Script byte operands and the full restored opcode family remain uncovered. |
| [442](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0442.md) | OP_PAIRCOMMIT | Draft | yes | bip442-paircommit computes the tagged, length-prefixed hash for elements up to 511 bytes; Script permits 520. |
| [443](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0443.mediawiki) | OP_CHECKCONTRACTVERIFY | Draft | yes | bip443-ccv-output and bip443-ccv-aggregate model output-key commitments and bounded amount aggregation; mode-complete compatibility remains unimplemented. |
| [446](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0446.md) | OP_TEMPLATEHASH | Draft | yes | bip446-templatehash-exact runs all 19 basics cases; newly vendored script_assets_test.json covers additional Script execution behavior and is not executed by this harness. |
| [448](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0448.md) | Taproot-native (Re)bindable Transactions | Draft | yes | bip448-lnsymmetry-update models template-bound update authorization; tapscript deployment/witness formats are outside the application. |
| [449](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0449.md) | OP_TWEAKADD - x-only key tweak addition | Draft | yes | bip449-tweakadd uses all generated passing/failing vectors embedded in the spec; curve lift/tweak operations already have jets. |
| [460](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0460.mediawiki) | CISA for Taproot Key Path Spends in SegWit v2 | Draft | keypath-adjacent | Cross-input signature aggregation changes SegWit-v2 key-path consensus and transaction-wide signature collection. Individual group operations are relevant, but a single input expression cannot validate the proposed global aggregation rule. |

## No-number proposals

This is a **documented search of the explicitly requested proposal families plus
adjacent proposals discovered through their original references**. It is not an
exhaustive enumeration of every bitcoindev email ever posted. Searches used the exact
opcode names and author references on bitcoindev, Delving Bitcoin, GitHub and the
linked M31 draft. The local source manifest gives URL, revision/message ID, license
status and full SHA-256 for every snapshot. The source text is data, never code to run.

| proposal | primary source and revision | verdict / missing primitive / coverage |
| --- | --- | --- |
| OP_EXPIRE | [Peter Todd original message, 2023-10-20](https://gnusha.org/pi/bitcoindev/ZTMWrJ6DjxtslJBn@petertodd.org/); [prototype discussion](https://delvingbitcoin.org/t/op-expire-mitigating-replacing-cycling-attacks/1282), first post v1 | **Needs consensus execution context.** The present Bitcoin primitive environment exposes transaction locktime and sequence, not current chain height, MTP or an enforced transaction expiry rule. A comparison to `nLockTime` alone cannot implement expiry. No misleading expiring-HTLC program is counted. Version/annex encodings and relay/maturity rules remain design choices. |
| OP_INOUT_AMOUNT / OP_IN_AMOUNT / OP_OUT_AMOUNT | [current-index draft at `92c108136a0400b3a2fd66ea6c291ec317ee4a01`](https://github.com/Christewart/bips/blob/92c108136a0400b3a2fd66ea6c291ec317ee4a01/bip-op-inout-amount.mediawiki); [Delving topic 549](https://delvingbitcoin.org/t/op-inout-amount/549), post 1 v2 and subsequent bitmap discussions | **Expressible with existing amount primitives and 64-bit arithmetic.** `op-inout-amount-withdrawal-cap` implements current-index amount release while preserving the output script. The later selected-input/output bitmap sums are distinct semantics and are not claimed by that entry. |
| OP_EVICT | [ZmnSCPxj original message, 2022-02-17](https://gnusha.org/pi/bitcoindev/6nZ-SkxvJLrOCOIdUtLOsdnl94DoX_NHY0uwZ7sw78t24FQ33QJlJU95W7Sk1ja5EFic5a3yql14MLmSAYFZvLGBS4lDUJfr8ut9hdB7GD4=@protonmail.com/) | **Expressible in the bounded native two-member profile.** [`app-op-evict-complete`](BITCOIN-GROWTH.md) binds two unique actual promised P2TR outputs and signatures, subtracts both keys from the actual internal key, and verifies the remaining key's spend signature. No exact Tapscript stack encoding, arbitrary member count, or upstream half-aggregation format claim. Key-cancellation-resistant group setup remains external. |
| TLUV | [overview](https://gnusha.org/pi/bitcoindev/20210909064138.GA22496@erisian.com.au/) and [details](https://gnusha.org/pi/bitcoindev/20210909065330.GB22496@erisian.com.au/), 2021-09-09 | `tluv-remove-leaf` implements one bounded removal/key-update mode. Control-word variants, point parity commitments and amount-preservation policy are explicit remaining scope. |
| 64-bit arithmetic | [PR 2073](https://github.com/bitcoin/bips/pull/2073), closed 2026-03-01; draft head `fd04d0a8a9d4dbb8a7ff14d8e94b1565067ecc0f`, CC0-1.0 | **Arithmetic expressible with existing jets.** `draft64-signed-widening-multiply` implements signed-64 operand bounds and a widened-128 product. This is the newer Script-number proposal, not the older fixed-width/overflow-flag design. Byte-level Script-number parsing and every opcode conversion are not covered. |
| OP_ZKP / OP_ZKPVERIFY | [Weiji Guo original message, 2023-04-29](https://www.mail-archive.com/bitcoin-dev%40lists.linuxfoundation.org/msg12601.html) | **Scheme-dependent, no pinned complete opcode specification.** The proposal discusses Groth16-BN254, public-input transaction binding and verification-key lookup. BN254 arithmetic is a relevant demand signal; P2P verification-key lookup cannot be synthesized inside a deterministic input expression. A Groth16 estimate is not an implementation of this opcode. |
| OP_STARK_VERIFY / OP_GROTH16_VERIFY | [Abdelhamid Bakhta, topic 2056](https://delvingbitcoin.org/t/proposal-op-stark-verify-native-stark-proof-verification-in-bitcoin-script/2056), post 1 v4, updated 2025-11-25 | **Verifier family not consensus-pinned.** Draft favors a bounded Stone-format vanilla STARK and leaves verifier IDs/parameters/size limits open. The M31/Circle or Fibonacci corpus verifier measures reusable arithmetic, hashing and FRI demand; it is not claimed to implement Stone byte compatibility. |
| M31 arithmetic opcodes | [author's linked draft](https://hackmd.io/@AbdelStark/m31-opcodes-bitcoin-stark) | **Expressible ordinary M31 arithmetic; candidate primitive jets measured separately.** Snapshot is hash-pinned because the HackMD URL is mutable. No published upstream test-vector file was discovered through the draft's references. |
| OP_CHECKINPUTVERIFY (CIV) | [Tadge Dryja original message, 2025-11-01](https://gnusha.org/pi/bitcoindev/05195086-ee52-472c-962d-0df2e0b9dca2n@googlegroups.com/) | **Expressible with existing `input_prev_outpoint`.** `op-civ-linked-input` authenticates a committed sibling outpoint at a witness-selected index, including wrong/missing/reordered input cases. The sibling input's authorizing signature remains that input's responsibility. |
| OP_TX and companion new-opcode draft | [Rusty Russell original OP_TX, 2025-09-27](https://gnusha.org/pi/bitcoindev/87y0q0m8vz.fsf@rustcorp.com.au/); [new-opcodes message](https://gnusha.org/pi/bitcoindev/87tt0om8uz.fsf@rustcorp.com.au/) | **Partial introspection coverage, full selector interpreter unimplemented.** Existing transaction primitives cover many fields, but raw input/output scripts require checked preimages and confirmation-height/current-chain context is not exposed. The proposed Script instruction family is not treated as a single monolithic jet. |

No explicit license statement was found in the Todd, Towns, ZmnSCPxj, Dryja and Guo messages or the HackMD draft; Rusty Russell’s embedded specifications state BSD-3-Clause.
The manifest states those facts instead of assigning a guessed license. The
OP_INOUT_AMOUNT draft has BSD-3-Clause in its header and a public-domain copyright
paragraph; both statements are preserved. Forum snapshots are archived with their
post IDs/versions and SHA-256, without assuming an unstated document-specific license.

## Upstream-vector accounting and remaining gaps

| BIP | available upstream data | execution coverage and limits |
| --- | --- | --- |
| 119 | `ctvhash.json`: 100 transaction objects, 400 transaction/index/hash pairs; also `tx_valid.json` and `tx_invalid.json` | The exact-digest program runs **all 193 in-range pairs**, plus two derived corruptions. The other **207** hashes request an index that cannot be the current input of the provided transaction, and therefore cannot instantiate `PrimEnv`; they are explicitly excluded. The native-digest comparator runs the same 193 transactions/indices with its own digest reference. The valid/invalid JSON files exercise full Script execution rather than only the digest and are vendored but unexecuted. |
| 346 | 150 published successful hash vectors | All 150 run through the expression; loading now fails if any successful upstream selector cannot decode. Eleven derived malformed-selector cases exercise the **Haskell decoder**, not the Simplicity expression. No upstream invalid-selector cases exist in this JSON. Context operands are not authenticated against Tapscript by the current Simplicity environment. |
| 347 | Three inline cases and pinned Bitcoin Core PR29247 JSON, C++ and activation tests | All 295 directly projectable upstream value operations and 47 derived vectors pass; all 34 CAT-related JSON rows inventoried. Node and full Script test harnesses were not executed. See [OP_CAT coverage](BIP347-OP-CAT.md). |
| 348 | BIP340 CSV, including invalid signatures and variable-length messages | Existing 19-vector CSFS entry and 15-vector 32-byte entry; the latter's restricted message length is intentional, not complete CSV coverage. |
| 360 | two construction JSON files, **16 cases** total: **13 successes**, **3 constructor errors**; 29 successful leaf openings | `tools/extract_bip360_vectors.py` independently checks every root, output script, control path and constructor error; `bip360-upstream-p2mr-output` executes all **29** leaf openings plus three derived corruptions. Bech32m encoding and Tapscript execution are not validated. The original Simplicity-CMR entry remains separate. |
| 446 | `basics.json` (19 cases) and `script_assets_test.json` | All 19 basics cases already execute. Additional Script assets are now vendored but require a full Script interpreter/translation and remain unexecuted. |
| 449 | generated passing/failing vectors embedded in the spec | Existing loader executes all embedded cases. Upstream Rust vector-generation code was discovered in the tree but is not needed or executed. |
| 54, 460 | consensus cleanup and CISA consensus/wallet vectors | Vendored to make the broad index filter reviewable; outside the single-input Script-computation corpus. |
| Other included BIPs | no separate `.json`/`.csv` vector assets found in the complete pinned tree | Complete specification text is vendored; existing entries use documented derived vectors or embedded vectors where present. This is an asset inventory statement, not a claim that every upstream reference repository has no tests. |

This inventory closes source-discovery ambiguity, not every implementation gap. In
particular unbounded EVICT compatibility, every CCV mode, byte-exact APO, the complete restored Script
instruction set, and Stone-compatible proof decoding remain distinguishable work.
