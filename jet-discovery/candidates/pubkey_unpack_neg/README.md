# Candidate: `pubkey_unpack_neg` — x-only public key parsing (negated)

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: A cheap parser primitive with small isolated savings in variable-key CSFS. Existing complete Schnorr jets hide the parser in many other entries, so benchmark the paired parser use before prioritizing.

Price: **0.656 WU (ESTIMATE)**. FeNormalize analogue: one field-range check and a parity tag; the coordinate is returned unchanged

Matches in 1 of 157 registered rows: 1 matched DAG nodes across all branches, 1 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bip348-csfs | native_full_verifier | 1 | 1 | 408.282 | 301.629 | 106.653 | yes / yes at 775 WU |

See the [complete matrix](../../reports/candidate-ranking.md#pubkey_unpack_neg) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`Word256 -> S (Bit, Word256)`

## Specification
The exact Simplicity expression is `Simplicity.Programs.LibSecp256k1.Lib.pubkey_unpack_neg`. For a raw integer x below the secp256k1 field prime p, return `Right (Right (), x)`, the odd-parity point encoding. Otherwise return `Left ()`. The x word is unchanged. Point decompression and curve membership are a separate operation. The Integer specification and the direct arrow test are in [Tests.hs](../../test/Tests.hs), with p from [Ref.Bip340](../../src/JetDiscovery/Ref/Bip340.hs).

## Cost (ESTIMATE)
**ESTIMATE:** `FeNormalize` = 0.656 WU, a benchmark analogue for inspecting one field-width word. The prototype returns an odd-parity tag and performs no coordinate arithmetic.

## Generality
Any signature check not built as `bip_0340_verify`: variable-length CSFS (BIP 348), adaptor signatures, MuSig2 and FROST partial checks, oracle attestations.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low. A C implementation compares the raw 256-bit input against p and writes the exact choice and odd-parity tag with the original x word on success. At the read-only `feat/jet-equivalence` revision `771d41b98acc3750308a07c76405125bbc8439cd`, `Coq/C/JET_ACCEPTANCE.md` lists `fe_normalize` and `fe_is_zero` as existing verified integrations. Their fixed-width field representation and exact output/frame relations inform the proof. The new proof must establish the raw range comparison and the sum/product encoding, with no curve-membership premise. The pinned acceptance document gives the local Clight proof scope and separates focused tip evidence from earlier whole-project acceptance.

## Alternatives considered
A variable-length `bip_0340_verify` (a message buffer instead of a 32-byte message) would make both unpack jets unnecessary for CSFS.
