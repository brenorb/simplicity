# Candidate: `pubkey_unpack_neg` — x-only public key parsing (negated)

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

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

## Corpus evidence
- `bip348-csfs`: matched ×1 (static multiplicity); program cost 408.282 WU → 87.927 WU with all candidates (4.6×).

The direct test covers zero, a valid generator key, both sides of p and the maximum raw word. It explicitly checks that x = 0 does not lift to the curve and still passes this unpacking arrow with odd parity. The CSFS vectors separately exercise the surrounding verifier.
