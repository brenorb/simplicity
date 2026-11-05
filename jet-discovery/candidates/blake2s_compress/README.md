# Candidate: `blake2s_compress` — BLAKE2s compression function

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`((Vector8 Word32, Vector16 Word32), (Word32, Word32)) -> Vector8 Word32` (final-block flag set)

## Specification
`JetDiscovery.Corpus.Hashes.blake2F blake2s`; passes the RFC 7693 Appendix B vector.

## Cost (ESTIMATE)
ESTIMATE: `Sha256Block` = 0.765 WU (similar work per 64-byte block).

## Generality
BLAKE2s, and BLAKE3 (same G function, 7 rounds, different flags); STARK commitment hashes (Stwo uses BLAKE2s).

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium. The structure is close to the proven SHA-256 compression: 32-bit add/xor/rotate rounds.

## Alternatives considered
A BLAKE3-specific compression jet would serve BLAKE3 directly. The final-block flag should become an input.

## Corpus evidence
- `xchain-blake2s-compress`: matched ×1 (static multiplicity); program cost 3256.768 WU → 4.330 WU with all candidates (752.1×).

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
