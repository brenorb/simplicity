# Actual scalar multiplication/write chain against the literal result

This milestone closes the arithmetic-to-Simplicity and arithmetic-to-writer
interfaces of the public multiplication proof. Starting with two normalized
scalar stores, the composed root derives the **actual original**
`secp256k1_scalar_mul(a,a,b)` and `write_scalar(dst,a)` calls in sequence and
the exact output
`outs0 ++ encode (canonical_scalar_multiply (a,b))` in the frame invariant.
The canonical term is the existing literal Core program, not a replacement
numeric specification. Numeric identities are internal adapters only.

## Checked contracts

- `four_words_scalar_limbs`: any four actual uint64 words are exactly the
  limbs recovered from their weighted value. It reuses the checked radix
  lemma and `Int64.repr_unsigned`; no exhaustive enumeration is needed.
- `scalar_writer_initial_rep_from_mul`: derives writer representation from
  the multiplication's actual post-free loads and output ownership. Exact
  `Vlong` loads, not only their decoded value, are retained.
- `scalar_mul_initial_rep_from_storage`: derives the two-region helper
  representation from actual scalar storage and Freeable permissions, with
  an explicit disjoint-operand condition. `scalar_mul_normalized_input_values`
  supplies both numeric equalities for that constructed rho.
- `eval_scalar_mul_literal_owned`: complete original scalar multiplication
  call producing writer-ready representation of the literal canonical result.
  Its normalization equalities are intermediate reader-bridge premises, not
  premises intended for the final public theorem.
- `eval_scalar_mul_write_literal`: complete multiplication then complete
  writer execution. The writer's input representation and post-multiplication
  invariant are **derived** in the same current memory. Its preconditions are
  input representation/normalized values, external-block separation, the
  existing output-frame invariant and 256 bits of remaining capacity; neither
  a helper execution nor output nor post-memory invariant is assumed.
- `eval_scalar_mul_write_from_normalized_storage`: same sequence starting
  from the two normalized scalar stores, discharging the symbolic helper
  representation and numeric equalities internally. It retains arbitrary
  valid output cursor/layout, existing output prefix, exact literal encoding,
  surviving destination ownership and outside-operands/external framing.

`jet_secp_scalar_writer_word.v` is reused **byte-for-byte** from the pending
scalar-add candidate. Its generic Word256 writer contract already existed;
this archive does not count it as a newly proved jet. The source path/hash is
pinned in the manifest. Promotion should share one `C` module, not register
two competing copies.

The composed postcondition does not yet expose the **second operand's**
Freeable permission after multiplication. That is a necessary interface
extension for the public wrapper's cleanup, not a C correctness finding.
The frame outside both operands cannot establish that permission by itself.

## Evidence and limits

Production/canonical source identity passed for 240 files; the immutable Coq
dependency fingerprint is unchanged. Full AST regeneration and integrated
acceptance were **not** run. Sources and drivers are durable here; the frozen
compiled artifacts and logs remain in the local scratch directory.

The reviewer also validates the earlier function/body/helper receipts and
exact reuse of the generic writer. Sixteen corruption fixtures operate only
in memory; they do not edit proofs or acceptance snapshots.
