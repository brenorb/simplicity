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

At the `1471be3d` integration baseline, `write_frame_at` requires every accessed word's exclusive end to be
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

## Normal-module generalization candidate

Branch `codex/write-word-endpoint` widens only the proof-side exclusive-end
bound in `write_frame` / `write_frame_at` and the bit/byte/wide raw writers.
The original C, specifications, API and generation settings are unchanged.
The original public constant, one, add and increment contracts at all four
arithmetic widths compile unchanged with the wider input predicate. Their
execution, encoded output, prefix, cursor and memory-framing conclusions are
unchanged. Whole-consumer rebuilding and acceptance are still required before
integrating this candidate.

`C.jet_word_endpoint_constants.last_word_frame_constructible` reuses the
archived memory construction for arbitrary initial contents of the final word.
`constants_run_at_last_word` applies the original complete public contracts for
all ten low/high jets, with an arbitrary environment argument, to that initial
memory. The actual C call and every output/framing observation are conclusions,
not premises. The frame witness retains four inherited assumptions and the
complete C executions retain the same six, without an added libc premise.
This is still an abstract-memory boundary witness, not a Linux allocation claim.

The new address definition is included in the existing definition audit. Its
theorem snapshots print without abbreviation: the framing interval is simplified
using the proved 1..64-bit width bound. No printer setting or checker gate is
relaxed. Reproduce normal compilation with:

```sh
JET_TARGETS=C/jet_word_endpoint_constants.vo bash Coq/build-jets.sh -j2
```

The first candidate at `10a1dc50` passes normal compilation and independent
recursive kernel checking of its 127-C-module closure. Existing no-update
assumption records across 32 modules and contract records across 43 modules
match; all 240 frozen inputs and the proof-source scan pass, with unchanged
verification inputs. No unsafe kernel features or extra library axioms occur.
This is not whole-consumer acceptance. The Bitcoin/Elements raw writer
transports now compile with only the same exclusive-end premises widened;
their axiom records are unchanged and the four recorded type changes are only
the added one-past byte. Whole-consumer compilation and checking remain pending.
It adds no registered jet and leaves the twenty unproved jets unresolved.
