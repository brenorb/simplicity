# Candidate: `pubkey_unpack_neg` — x-only public key parsing (negated)

## Type signature
`Word256 -> S (Bit, Word256)`

## Specification
The library's own `Simplicity.Programs.LibSecp256k1.pubkey_unpack_neg` (used inside `bip_0340_check`).

## Cost (ESTIMATE)
ESTIMATE: `FeNormalize` = 0.328 WU (a range check plus a negation).

## Generality
Any signature check not built as `bip_0340_verify`: variable-length CSFS (BIP 348), adaptor signatures, MuSig2 and FROST partial checks, oracle attestations.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low: a range check against p, similar to the proven `fe_normalize`/`fe_is_zero` jets.

## Alternatives considered
A variable-length `bip_0340_verify` (a message buffer instead of a 32-byte message) would make both unpack jets unnecessary for CSFS.

## Corpus evidence
<!-- EVIDENCE -->
