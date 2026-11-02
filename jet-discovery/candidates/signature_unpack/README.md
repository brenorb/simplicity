# Candidate: `signature_unpack` — BIP 340 signature parsing

## Type signature
`(Word256, Word256) -> S (Word256, Word256)`

## Specification
The library's `Simplicity.Programs.LibSecp256k1.signature_unpack` (r < p, s < n).

## Cost (ESTIMATE)
ESTIMATE: `FeNormalize` + `ScalarNormalize` = 0.578 WU.

## Generality
As for `pubkey_unpack_neg`.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low.

## Alternatives considered
See `pubkey_unpack_neg`.

## Corpus evidence
<!-- EVIDENCE -->
