# Writable-word exclusive-end support (unintegrated)

The later concrete witness is now complete as well:

`word-endpoint-witness.v.source` constructs a CompCert memory by allocating a
block ending at `max_unsigned + 1` and storing the metadata, cursor and an
arbitrary initial word. For either Boolean bit, it derives the full original
`writeBit` call, output/load/bit, prefix, cursor, outside loads, permissions and
block validity, and proves that the current `write_frame_at` rejects the initial
state. Thus the wider predicate's additional case is inhabited in the formal
memory model, not merely arithmetic or a conditional execution theorem.
This still does not assert reachability by the Linux allocator/evaluator.

The current `write_frame_at` requires every accessed word's exclusive end to be
at most `Ptrofs.max_unsigned`. The separate `endpoint_write_frame_at` changes
only that bound to `max_unsigned + 1`. All cursor, metadata, range-separation,
writable-access and initial-load requirements remain identical.

`word-endpoint-support.v.source` preserves six completed declarations:

- Original `writeBit` raw execution under the wider end bound.
- Head address/access and metadata/data separation projection lemmas.
- Total original `writeBit` execution from the widened initial predicate,
  retaining output bit/load, prefix, cursor, outside loads, permissions and
  existing block validity.
- Inclusion of every old initial contract in the widened contract.
- A closed arithmetic witness: the final aligned 64-bit word begins at
  `18446744073709551608`, has representable start, and ends exclusively at
  `max_unsigned + 1`, not at or below `max_unsigned`.

The total theorem derives both stores from initial valid access; it does not
assume helper execution or output. The raw theorem is internal support and
retains explicit store premises. Actual generated C/AST bodies are unchanged.

Fresh compilation passes (97445 and final 38503); the final independent
whole-chain kernel check passes with exit 0 (38503), using Coq 8.17.1 and a
65520 KiB stack. Its 15 library axioms match the inherited kernel allowlist;
type-in-type, unsafe fixpoints and assumed positivity are all absent. The
arithmetic witness is closed; the execution theorem retains six inherited
assumptions. This does not certify a reachable Linux allocation at that address.

Reproducible checks from that dependency directory, with the project Coq PATH:

The two running checkout/negation audits are not modified by this work. No
accepted predicate or coverage changes. Generalizing the accepted shared
contract still requires the other reader/writer/pointer/copy callers, actual
domain review, reviewed snapshot differences and separate full acceptance.
Reuse the successful bit-writer proof; do not infer that widening its bound
automatically repairs every dependent caller or the evaluator boundary.
