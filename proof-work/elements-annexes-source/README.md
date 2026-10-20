# Canonical Elements annex-loop source review

The fixed model checks26 whole Coq declarations/statements plus four
Reader/context/annex-helper blocks. It is not regenerated during checking.
The inherited seven-stream-getter guard covers the actual Elements SigHash
library body, word/SHA loops, primitive port, native word/hash representation,
and the general application/getter contracts.

This extension follows `InputAnnexesHash` through the catalog and wrapper to
the canonical 32-bit `InputAnnexHash` loop, follows `annexHash` through the
Elements library selector, and checks that its body is the same zero/one-marker
program as the reused Bitcoin helper. It pins the raw optional-annex mapping,
the original C getter, and the entire final C-to-program theorem, including
the correct transaction hash offset376, logical environment and frame relation.

Tests cover absent/present option distinction, marker changes, primitive/SHA
selection, iteration bounds, generic helper assumptions, C field selection,
wrong or vacuous endpoint contracts, and string-literal namespace drift.
One initial fixture hit an earlier nonce marker; it was narrowed to the actual
annex clause. That was a test-targeting correction, not a C/spec mismatch.

This is executable source-boundary review, not a formal verification of host
Haskell/lens/cryptography libraries. It does not establish caller cache setup,
claim a kernel result, register a jet or constitute full normal acceptance.
