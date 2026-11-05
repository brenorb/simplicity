# Candidate: `blake2b_compress` — BLAKE2b compression function (EIP-152 F)

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`((Vector8 Word64, Vector16 Word64), (Word64, Word64)) -> Vector8 Word64`

## Specification
`JetDiscovery.Corpus.Hashes.blake2F blake2b`; passes RFC 7693 Appendix A.

## Cost (ESTIMATE)
ESTIMATE: 1.5 x `Sha256Block` = 1.147 WU (128-byte blocks, 64-bit words, 12 rounds).

## Generality
Zcash (Equihash, BLAKE2b personalization), Ethereum EIP-152 interoperability, Argon2.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium, like BLAKE2s with 64-bit words.

## Alternatives considered
EIP-152 exposes the round count as an input; a jet could too.

## Corpus evidence
- `xchain-blake2b-compress`: matched ×1 (static multiplicity); program cost 4641.718 WU → 11.381 WU with all candidates (407.8×).
- Mining: BLAKE2b's G function (38.5 WU) x96 is 79.6% of `xchain-blake2b-compress`.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
