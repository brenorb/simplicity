# Borrowed-region foundation for constant field operands

Seven helper lemmas are freshly compiled and recursively kernel-checked against
the unchanged checked regular-module basis. They establish that changing a
region to non-owning/read-only metadata preserves its cells and symbolic loads,
rejects symbolic writes to that region, and weakens the existing cell/region
memory contracts without upgrading any permission or changing memory.

This is **not** a proof of `fe_multiply_beta` or of a complete borrowed-input
function call. The old field-multiplier caller requires Freeable inputs; a
read-only global cannot satisfy that contract. These lemmas do not pretend it
can. Next, lift the actual symbolic execution through this metadata change for
an operand region the function never writes, reuse the existing arithmetic and
range proofs, then establish the actual beta global's initialized contents and
compose the real caller. Keep its full input domain and frame contract.

The first compiler probe needed a beta-convertible `change` before rewriting
`nth_error_map`; the actual interactive hypothesis was inspected before fixing
it. The first audit expectation incorrectly required all seven results to be
closed. That terminal profile-check failure, its original checker and the actual
five-closed/two-inherited profile are preserved separately. The proof statements
were not weakened and the proof source did not change to accommodate the audit.
The successful exact-profile check is a distinct recorded attempt.
