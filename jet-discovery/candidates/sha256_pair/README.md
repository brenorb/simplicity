# Candidate: `sha256_pair` — SHA-256 of a 64-byte concatenation

## Type signature
`Word512 -> Word256`

## Specification
`JetDiscovery.Lib.Kernels.sha256Pair`: one Merkle-node hash (OP_CAT + OP_SHA256 in Script).

## Cost (ESTIMATE)
ESTIMATE: 2 x `Sha256Block` = 1.530 WU.

## Generality
Merkle paths (tree signatures, STARK commitments, BitVM, any SHA-256 Merkle tree).

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low. It is a composition of proven jets (`sha256_ctx_8_init`, `add_64`, `finalize`); the proof is mostly gluing existing lemmas.

## Alternatives considered
Today it is three jets plus plumbing; a "hash two 32-byte nodes" jet with a tag or sort option would also serve BIP 341 TapBranch-style trees.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
