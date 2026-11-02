# Candidate: `blake2b_compress` — BLAKE2b compression function (EIP-152 F)

## Type signature
`((Vector8 Word64, Vector16 Word64), (Word64, Word64)) -> Vector8 Word64`

## Specification
`JetDiscovery.Corpus.Hashes.blake2F blake2b`; passes RFC 7693 Appendix A.

## Cost (ESTIMATE)
ESTIMATE: 1.5 x `Sha256Block` = 0.574 WU (128-byte blocks, 64-bit words, 12 rounds).

## Generality
Zcash (Equihash, BLAKE2b personalization), Ethereum EIP-152 interoperability, Argon2.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium, like BLAKE2s with 64-bit words.

## Alternatives considered
EIP-152 exposes the round count as an input; a jet could too.

## Corpus evidence
<!-- EVIDENCE -->
