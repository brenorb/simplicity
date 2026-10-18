# Original Elements entropy frame jet

`calculate_issuance_entropy_local_spec` proves execution of the unchanged
`simplicity_calculate_issuance_entropy`, returning true and writing exactly
the canonical `calculate_issuance_entropy_spec` Simplicity word program.
It composes the actual five allocations, source-frame copy, complete 544-bit
input prefix, original entropy helper, struct result copy, original
`writeHash`, return conversion and every local free. The contract also proves
the advanced destination cursor, preservation of the output prefix, and
unchanged loads outside the permitted destination ranges.

Input is `((Word256, Word32), Word256)` and output is Word256. Valid arbitrary
cursors, boundary crossings and pre-existing output bits are supported. The
input cursor's final value is used only inside the copied local source frame;
the caller's source frame is not advanced by this by-value argument.

The explicit assumptions are the existing `memcpy_model`, the actual Elements
SHA dispatch and maximum-counter loads, and represented readable/writable
frames. No desired helper execution, cached result, output value, allocation,
store or local-free result is an initial premise. Startup and frame
constructibility corollaries are subsequent work, not claimed here.

`Common.v.source` reuses the already-proved generic calculation statement
lemmas, with a generic source-copy environment and the exact entropy entry
size lemma. `Writer.v.source` is unchanged from the earlier checked
calculation-jet writer. The Coq proof-engineering skill guided the separation
of statement execution, representation, memory preservation and public
composition. One over-broad cleanup simplification was narrowed to the local
block list; no theorem, C code or specification was changed to make it pass.

`verify.py compile|kernel EXTERNAL_DIRECTORY` freshly compiles all five
modules, checks full statements/definitions and the exact 27-result profile
(12 closed, four four-dependency, eleven six-dependency results; the public
endpoint has the six inherited assumptions), and binds every loaded project
module to the 278-source helper basis. All nine inherited and five new
extension source/object pairs are checked as well. Compilation and recursive
kernel checking have separate receipts; only `CHECKED.json` establishes the
latter. Nothing is normally registered and accepted coverage added is zero.
