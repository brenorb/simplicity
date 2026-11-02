# Candidate: `keccak_f1600` — Keccak-f[1600] permutation

## Type signature
`Vector32 Word64 -> Vector32 Word64` (25 lanes used)

## Specification
`JetDiscovery.Corpus.Hashes.keccakF`: 24 rounds of theta, rho, pi, chi, iota; passes the Keccak-256 known answers for "" and "abc".

## Cost (ESTIMATE)
ESTIMATE: 2 x `Sha256Block` = 0.765 WU. Software Keccak-f[1600] takes roughly twice a SHA-256 compression without hardware acceleration.

## Generality
Primitive for Ethereum interoperability (Keccak-256 addresses, storage proofs, bridge light clients), SHA-3/SHAKE (FIPS 202) and some STARK hash choices.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium to high. It is a new permutation, but a regular one: fixed rounds of 64-bit xor/and/not/rotate. The 64-bit word-jet proofs and the symbolic-execution approach used for SHA-256 apply; the state is large (1600 bits).

## Alternatives considered
Keeping it in Simplicity costs about 240 WU per round.

## Corpus evidence
- `xchain-keccak256`: matched ×1 (static multiplicity); program cost 5775.502 WU → 24.296 WU with all candidates (237.7×).
- Mining: one Keccak round (`W2048 -> W2048`, 237.5 WU) x24 is 98.7% of `xchain-keccak256`.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
