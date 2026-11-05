# Candidate: `blake2b_compress` — fixed-round, final-block BLAKE2b compression

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`((Vector8 Word64, Vector16 Word64), (Word64, Word64)) -> Vector8 Word64`

## Specification
`JetDiscovery.Corpus.Hashes.blake2F blake2b` takes eight chaining words, sixteen block words and the two counter words. It runs twelve rounds with the final-block flag set. The RFC 7693 Appendix A case is covered by the reference test.

## Cost (ESTIMATE)
ESTIMATE: 1.5 x `Sha256Block` = 1.147 WU (128-byte blocks, 64-bit words, 12 rounds).

## Generality
Zcash (Equihash, BLAKE2b personalization), the twelve-round final-block portion of Ethereum EIP-152, Argon2.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium. A C implementation can use sixteen 64-bit state words with fixed add, XOR, and rotate operations. The read-only `feat/jet-equivalence` revision `771d41b98acc3750308a07c76405125bbc8439cd` has `Coq/C/jet_add64_wide_word.v` and `Coq/C/jet_right_rotate_wide_word.v` with proof snapshots for the modular addition payload and 64-bit rotate relation. The new proof must connect those operations to the BLAKE2b state initialization, both counter words, the fixed final-block flag, all twelve message schedules, and feed-forward. The word lemmas cover components of that work.

## Alternatives considered
A wider interface could expose the round count and the final-block flag, as EIP-152 does. That would require a different arrow, bound and proof.

## Corpus evidence
- `xchain-blake2b-compress`: matched ×1 (static multiplicity); program cost 4641.718 WU → 11.381 WU with all candidates (407.8×).
- Mining: BLAKE2b's G function (38.5 WU) x96 is 79.6% of `xchain-blake2b-compress`.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
