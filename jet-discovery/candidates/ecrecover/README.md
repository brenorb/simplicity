# ecrecover

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: The Ethereum-style bridge, permit and oracle paths benefit. In the quorum example the combined estimate with Keccak fits where either candidate alone does not. Benchmark reusable recovery to a point plus a separate permutation before fixing the Ethereum address and failure ABI.

Price: **107.232 WU (ESTIMATE)**. ESTIMATE: existing secp256k1 operation benchmarks plus Keccak priced as 2 x Sha256Block

Matches in 6 of 157 registered rows: 6 matched DAG nodes across all branches, 43 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| xchain-eip712-permit | protocol_component | 1 | 1 | 24,042.559 | 18,005.712 | 6,036.847 | no / no at 6170 WU |
| xchain-wormhole-13-of-19 | native_full_verifier | 19 | 1 | 128,724.783 | 14,024.690 | 114,700.093 | no / no at 5955 WU |
| xchain-ecrecover | native_full_verifier | 1 | 1 | 6,147.718 | 110.871 | 6,036.847 | no / yes at 3734 WU |
| app-permit2-bitmap-transfer | native_full_spend | 1 | 1 | 37,217.352 | 31,180.505 | 6,036.847 | no / no at 10154 WU |
| app-vaa-bridge-replay-payout | native_full_spend | 19 | 1 | 136,523.527 | 21,823.434 | 114,700.093 | no / no at 12721 WU |
| app-ocr-report-state-machine | native_full_spend | 2 | 1 | 31,208.149 | 19,134.455 | 12,073.694 | no / no at 8566 WU |

See the [complete matrix](../../reports/candidate-ranking.md#ecrecover) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

Prototype only; no consensus registration.

- **Type:** `(Word256, (Word256, (Word256, Bit))) -> Word256`, interpreted as `(z, (r, (s, recoveryParity)))`; result is a 160-bit Ethereum address zero-extended to 256 bits. Parity corresponds to Ethereum v=27/28. EIP155 transaction-v decoding is outside this function.
- **Reference expression:** `JetDiscovery.Corpus.ContractExpansion.ecRecover`: require canonical nonzero r,s below n, decompress R with x=r and the supplied parity, compute `r^-1(sR-zG)`, reject infinity, normalize Q, hash `x(Q)||y(Q)` using Keccak256, and retain the low160 bits. This is Ethereum's x=r recovery convention, not generic SEC1 recovery IDs2/3.
- **Haskell specification:** Integer secp256k1 arithmetic in `Ref.Bip340`, with independently written `Ref.Keccak`. Tests check standard Keccak digests plus recovery against independently generated ECDSA signatures; corpus vectors include wrong parity, changed digest and malformed scalars.
- **Evidence:** `xchain-ecrecover`, `xchain-eip712-permit`, and `xchain-wormhole-13-of-19`. Wormhole has19 statically present optional slots, so static cost accounts for the worst branch at every slot. Runtime vectors need13 actual signers. Generated mining and what-if reports are authoritative for occurrence counts and savings.
- **Cost: ESTIMATE.** Overlay method: sum the in-tree benchmark-derived costs of `ScalarInvert`, `Decompress`, `LinearCombination1`, `GejNormalize`, `ScalarNegate`, twice `ScalarMultiply`, and twice `Sha256Block`. SHA256 compression is only a pricing proxy for Keccak work; the existing measured Keccak reference is not itself benchmarked native code. This uncertainty must remain visible in rankings.
- **Budget effects:** `reports/whatif.md` gives per-program measured-reference/estimated-overlay costs and savings after a full corpus run. Budget claims remain conditional on `reports/METHOD.md`'s assumption.
- **Generality:** Ethereum permits, guardian bridges and existing Ethereum-address oracle identities. The benefit over ECDSA verify depends on whether an application really needs the recovered address rather than a known public key.
- **Verification burden: high.** Read-only analogues on `feat/jet-equivalence`: Schnorr verification, point decompression, `linear_combination_1`, scalar inversion and field normalization. C complexity is moderate using libsecp256k1 recovery plus Keccak; Coq work additionally needs recovery uniqueness under Ethereum's convention, affine serialization, Keccak correctness and low160-bit extraction. No existing SHA256 proof establishes Keccak.
- **Alternatives:** known-public-key ECDSA verification avoids recovery and address hashing; a separate reusable Keccak permutation jet may serve more applications. Compare those alternatives using the measured overlays rather than assuming one combined jet is best.

Read-only proof evidence inspected at `feat/jet-equivalence` (`771d41b98acc3750308a07c76405125bbc8439cd`): `Coq/C/JET_ACCEPTANCE.md` records checked linear-combination acceptance at `6491c8b6`; `Coq/C/JET_PROOF_BACKLOG.md` records BIP340 acceptance at `740a5536` and its exact-input limits. These are analogies for proof structure, not evidence that either new candidate is proved. No existing proof source was edited.
