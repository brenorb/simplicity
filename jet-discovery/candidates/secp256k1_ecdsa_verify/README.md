# secp256k1_ecdsa_verify

Prototype only; no consensus jet, encoding, cost or existing implementation changes.

- **Type:** `(((Word256, Word256), Word256), (Word256, Word256)) -> ()`, interpreted as `((Q, z), (r, s))`.
- **Reference expression:** `JetDiscovery.Corpus.ContractExpansion.ecdsaVerify`. It checks canonical public-key coordinates, the curve equation, `1 <= r,s < n`, computes the scalar inverse, forms `(z/s)G + (r/s)Q`, rejects infinity, and compares the affine x-coordinate modulo n with r. High s is accepted, as mathematical ECDSA permits it.
- **Haskell specification:** SEC1 verification with `JetDiscovery.Ref.Bip340` Integer point arithmetic; candidate tests in `test/Tests.hs` independently sign and mutate messages. Corpus vectors additionally reject zero/noncanonical scalars and malformed public keys.
- **Evidence:** `xchain-secp256k1-ecdsa` and the generated exact/shape sub-DAG tables. Ethereum recovery paths use a related, different expression and are not automatically counted as ECDSA matches. Occurrences and per-program savings come from `reports/whatif.md`; do not infer them by name.
- **Cost: ESTIMATE.** The overlay sums the in-tree benchmark-derived `cost` values for `ScalarInvert`, `LinearCombination1`, `GejNormalize`, `GeIsOnCurve` and `ScalarNormalize`. This is a composition-based estimate, not an implemented C benchmark. It omits some range-check/overhead cost and must be revisited before any consensus recommendation.
- **Budget effects:** reproducible `jet-discovery run` produces the measured original and estimated overlay costs. Feasibility uses the explicitly assumed witness budget in `reports/METHOD.md`, not a claimed Bitcoin consensus rule.
- **Generality:** legacy ECDSA authorization, Ethereum-compatible signatures, EIP712 permits and external oracle protocols. Prefer this over an application-specific signature format when ECDSA verification is the repeated workload.
- **Verification burden: medium/high.** Closest proof patterns on the read-only `feat/jet-equivalence` branch are `bip_0340_verify`, `linear_combination_1`, scalar inversion and normalization. C can compose libsecp256k1 ECDSA primitives, but strict canonical decoding, x modulo n, high-s behavior and infinity checks require an exact equivalence argument. Existing Schnorr proofs supply group/arithmetic lemmas, not the ECDSA theorem itself.
- **Alternative:** compose existing secp256k1 jets, as the executable reference does. A monolithic jet is justified only if measured dispatch/normalization savings exceed its proof and maintenance burden.

Read-only proof evidence inspected at `feat/jet-equivalence` (`771d41b98acc3750308a07c76405125bbc8439cd`): `Coq/C/JET_ACCEPTANCE.md` records checked linear-combination acceptance at `6491c8b6`; `Coq/C/JET_PROOF_BACKLOG.md` records BIP340 acceptance at `740a5536` and its exact-input limits. These are analogies for proof structure, not evidence that either new candidate is proved. No existing proof source was edited.
