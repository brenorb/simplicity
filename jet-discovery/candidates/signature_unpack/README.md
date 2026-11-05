# Candidate: `signature_unpack` — BIP 340 signature parsing

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`(Word256, Word256) -> S (Word256, Word256)`

## Specification
The exact Simplicity expression is `Simplicity.Programs.LibSecp256k1.Lib.signature_unpack`. Return `Right (r,s)` with both words unchanged when r is below the secp256k1 field prime p and s is below the scalar order n. Return `Left ()` otherwise. This arrow accepts zero components in range and performs no signature equation. The Integer specification and direct arrow test are in [Tests.hs](../../test/Tests.hs), with p and n from [Ref.Bip340](../../src/JetDiscovery/Ref/Bip340.hs).

## Cost (ESTIMATE)
ESTIMATE: `FeNormalize` + `ScalarNormalize` = 1.156 WU.

## Generality
As for `pubkey_unpack_neg`.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low. A C implementation compares the two raw 256-bit words with p and n, writes the exact choice tag, and copies both unmodified words on success. At the read-only `feat/jet-equivalence` revision `771d41b98acc3750308a07c76405125bbc8439cd`, `Coq/C/JET_ACCEPTANCE.md` lists `fe_normalize` and `scalar_normalize` as existing verified integrations. Their fixed-width field/scalar representation and exact output/frame relations inform the proof. The new proof must establish both raw range comparisons and the joint sum/product encoding. The pinned acceptance document gives the local Clight proof scope and separates focused tip evidence from earlier whole-project acceptance.

## Alternatives considered
See `pubkey_unpack_neg`.

## Corpus evidence
- `bip348-csfs`: matched ×1 (static multiplicity); program cost 408.282 WU → 87.927 WU with all candidates (4.6×).

The direct test evaluates 64 pairs spanning zero, the distinct field/scalar boundaries, and maximum raw words. The CSFS vectors separately exercise the surrounding verifier.
