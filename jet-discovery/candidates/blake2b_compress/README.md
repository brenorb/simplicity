# Candidate: `blake2b_compress` — fixed-round, final-block BLAKE2b compression

## Type signature
`((Vector8 Word64, Vector16 Word64), (Word64, Word64)) -> Vector8 Word64`

## Specification
`JetDiscovery.Corpus.Hashes.blake2F blake2b` takes eight chaining words, sixteen block words and the two counter words. It runs twelve rounds with the final-block flag set and eight G mixes per round, for 96 source-level mixes. The RFC 7693 Appendix A case is covered by the reference test.

## Cost (ESTIMATE)
ESTIMATE: 1.5 x `Sha256Block` = 1.147 WU (128-byte blocks, 64-bit words, 12 rounds).

## Generality
Zcash (Equihash, BLAKE2b personalization), the twelve-round final-block portion of Ethereum EIP-152, Argon2.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium. A C implementation can use sixteen 64-bit state words with fixed add, XOR, and rotate operations. The read-only `feat/jet-equivalence` revision `771d41b98acc3750308a07c76405125bbc8439cd` has `Coq/C/jet_add64_wide_word.v` and `Coq/C/jet_right_rotate_wide_word.v` with proof snapshots for the modular addition payload and 64-bit rotate relation. The new proof must connect those operations to the BLAKE2b state initialization, both counter words, the fixed final-block flag, all twelve message schedules, and feed-forward. The word lemmas cover components of that work.

## Alternatives considered
A wider interface could expose the round count and the final-block flag, as EIP-152 does. That would require a different arrow, bound and proof.

## Reference checks

The standalone probe matches all 40 inputs against a separate Word64 implementation of RFC 7693 F in both raw and existing-jet-substituted Simplicity evaluation. It checks the published Appendix A state, arbitrary chaining and block words, and high and low counter boundaries with the final-block flag set. [Probe](../../tools/CheckBlake2bCandidate.hs) · [Results](../../reports/data/blake2b-candidate-reference-probe.txt) · [Provenance](../../reports/data/blake2b-candidate-reference-provenance.json)
