# Candidate: `pubkey_unpack_neg` — x-only public key parsing (negated)

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`Word256 -> S (Bit, Word256)`

## Specification
The library's own `Simplicity.Programs.LibSecp256k1.pubkey_unpack_neg` (used inside `bip_0340_check`).

## Cost (ESTIMATE)
ESTIMATE: `FeNormalize` = 0.656 WU (a range check plus a negation).

## Generality
Any signature check not built as `bip_0340_verify`: variable-length CSFS (BIP 348), adaptor signatures, MuSig2 and FROST partial checks, oracle attestations.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low: a range check against p, similar to the proven `fe_normalize`/`fe_is_zero` jets.

## Alternatives considered
A variable-length `bip_0340_verify` (a message buffer instead of a 32-byte message) would make both unpack jets unnecessary for CSFS.

## Corpus evidence
- `bip348-csfs`: matched ×1 (static multiplicity); program cost 408.282 WU → 87.927 WU with all candidates (4.6×).

Test: the specification is the library's own function; `bip348-csfs` runs it on all 19 BIP 340 vectors, including invalid keys (rows 5, 14) and out-of-range signatures (rows 11-13).
