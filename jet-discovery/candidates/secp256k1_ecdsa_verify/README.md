# secp256k1_ecdsa_verify

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: Known-key ECDSA can reuse existing curve proofs. The corpus separates client signatures and native predicates, and the current price omits two scalar multiplications and range/control work. Benchmark exact affine and scalar checks first.

Price: **94.293 WU (ESTIMATE)**. Sum of ScalarInvert, LinearCombination1, GejNormalize, GeIsOnCurve and ScalarNormalize benchmark analogues. This ESTIMATE omits two separate scalar multiplications and range/control overhead.

Matches in 3 of 157 registered rows: 3 matched DAG nodes across all branches, 7 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| app-numeric-dlc-adaptor-cet | client | 2 | 1 | 4,083.550 | 3,787.228 | 296.322 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor | client | 4 | 1 | 5,679.600 | 5,086.956 | 592.644 | n/a (client) |
| xchain-secp256k1-ecdsa | native_full_verifier | 1 | 1 | 245.314 | 97.153 | 148.161 | yes / yes at 706 WU |

See the [complete matrix](../../reports/candidate-ranking.md#secp256k1_ecdsa_verify) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

Prototype only; no consensus jet, encoding, cost or existing implementation changes.

- **Type** `(((Word256, Word256), Word256), (Word256, Word256)) -> ()`, interpreted as `((Q, z), (r, s))`. The caller supplies raw affine coordinate words, the digest word, and the two signature words. DER decoding, public-key decompression, transaction digest construction, and signature policy belong to the caller.
- **Reference expression:** `JetDiscovery.Corpus.ContractExpansion.ecdsaVerify`. It checks canonical public-key coordinates, the curve equation, `1 <= r,s < n`, computes the scalar inverse, forms `(z/s)G + (r/s)Q`, rejects infinity, and compares the affine x-coordinate modulo n with r. High s is accepted, as mathematical ECDSA permits it.
- **Haskell specification:** SEC1 verification with `JetDiscovery.Ref.Bip340` Integer point arithmetic; candidate tests in `test/Tests.hs` independently sign and mutate messages. Corpus vectors additionally reject zero/noncanonical scalars and malformed public keys.
- **Evidence:** `xchain-secp256k1-ecdsa` and the generated exact/shape sub-DAG tables. Ethereum recovery paths use a related, different expression and are not automatically counted as ECDSA matches. Occurrences and per-program savings come from `reports/whatif.md`; do not infer them by name.
- **Cost estimate.** The current overlay sums the benchmark-derived prices of `ScalarInvert`, `LinearCombination1`, `GejNormalize`, `GeIsOnCurve`, and `ScalarNormalize`. It uses that sum as an **ESTIMATE**. The reference also executes two `ScalarMultiply` calls for `z/s` and `r/s`, along with coordinate and scalar range checks, equality, and control overhead. The proxy leaves those operations unpriced as separate components. A C benchmark should price the complete arrow, including its accepted high-s inputs and invalid-input paths. [Reference expression](../../src/JetDiscovery/Corpus/ContractExpansion.hs)
- **Budget effects:** reproducible `jet-discovery run` produces the measured original and estimated overlay costs. Feasibility uses the explicitly assumed witness budget in `reports/METHOD.md`, not a claimed Bitcoin consensus rule.
- **Generality** Known-public-key ECDSA authorization and oracle reports share this arrow. Address-based permits use public-key recovery and address derivation where the contract authenticates an Ethereum address. The current exact matches for those paths are tracked separately under recovery and Keccak.
- **Verification burden: medium/high.** Closest proof patterns on the read-only `feat/jet-equivalence` branch are `bip_0340_verify`, `linear_combination_1`, scalar inversion and normalization. C can compose libsecp256k1 ECDSA primitives, but strict canonical decoding, x modulo n, high-s behavior and infinity checks require an exact equivalence argument. Existing Schnorr proofs supply group/arithmetic lemmas, not the ECDSA theorem itself.
- **Alternative:** compose existing secp256k1 jets, as the executable reference does. A monolithic jet is justified only if measured dispatch/normalization savings exceed its proof and maintenance burden.

Read-only proof evidence inspected at `feat/jet-equivalence` (`771d41b98acc3750308a07c76405125bbc8439cd`): `Coq/C/JET_ACCEPTANCE.md` records checked linear-combination acceptance at `6491c8b6`; `Coq/C/JET_PROOF_BACKLOG.md` records BIP340 acceptance at `740a5536` and its exact-input limits. These are analogies for proof structure, not evidence that either new candidate is proved. No existing proof source was edited.
