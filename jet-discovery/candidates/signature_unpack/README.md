# Candidate: `signature_unpack` — BIP 340 signature parsing

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`(Word256, Word256) -> S (Word256, Word256)`

## Specification
The library's `Simplicity.Programs.LibSecp256k1.signature_unpack` (r < p, s < n).

## Cost (ESTIMATE)
ESTIMATE: `FeNormalize` + `ScalarNormalize` = 1.156 WU.

## Generality
As for `pubkey_unpack_neg`.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low.

## Alternatives considered
See `pubkey_unpack_neg`.

## Corpus evidence
- `bip348-csfs`: matched ×1 (static multiplicity); program cost 408.282 WU → 87.927 WU with all candidates (4.6×).

Test: the specification is the library's own function; `bip348-csfs` runs it on all 19 BIP 340 vectors, including invalid keys (rows 5, 14) and out-of-range signatures (rows 11-13).
