# Input-independent null-data environment and complete call

## Environment relation and endpoint

`elements_null_data_environment_rep m env environment fp` describes the entire
physical environment used by this jet independently of the chosen Word32 input
pair, destination frame and Bit Machine layout. It records initial C loads and
non-wrapping addresses: the transaction pointer and output count; each present
output's array pointer and null-data flag; and, only for successfully parsed
scripts, the parsed count and each present opcode's pointer/code. Push data
additionally has the cached canonical SHA words. The finite `fp` contains all
those read intervals. It contains no C execution, desired output, final memory,
frame aliasing or post-write representation premise.

`elements_null_data_environment_specialize` derives the old per-input output
representation, physical opcode case and logical script-lookup correspondence
from that single relation plus environment/output footprint separation. The C
output count bound follows from the logical transaction's existing Word32 bound;
it is not an additional axiom or chosen-index premise. The proof handles output
lookup failure, non-null-data scripts, successful parsing, absent opcode indices
and all datum constructors through the checked generic opcode representation.

`elements_output_null_datum_environment_bitmachine` combines this with the
complete C-to-primitive and Bit Machine proofs. Its only environment premises
are the input-independent representation and separation of its footprint from
the active output. The other premises are the existing represented/separated
Bit Machine, write permissions, canonical input prefix and output capacity.
It returns the actual complete CompCert call, canonical primitive result and
representation of the expected output state with every other frame preserved.

## Nullable cases and remaining caller work

An empty output list does not require loading `tx->output`. A non-null-data
script does not require a parsed count/pointer/cache. An empty parsed list or
missing selected datum does not require an opcode pointer. Non-push datums do
not require a cached hash. The relation describes only what this C jet reads;
unrelated fields, padding and bits are unconstrained.

The representation is a physical/cache correspondence condition, not yet a
proof that the actual Elements environment builder establishes it. In
particular, opcode parsing and cached SHA values must still be connected to
the real builder before claiming caller-established correspondence. Nor does
this batch prove representation invariant maintenance by the real C evaluator.

The theorem is explicitly for represented/separated evaluator frames, not
unrestricted overlapping buffers or the broader old
`application_jet_local_spec_sep`. Next expose the exact contextual contract in
shared infrastructure, review Haskell/Coq-port source fidelity (including the
null-data parser and encoding), and apply normal admission without disguising
the domain distinction. The header/API aliasing question remains open in
`../null-data-overlap-probe/README.md`.

The target remains the pinned assertion-disabled Elements program. No C,
header, canonical primitive, main registry or acceptance snapshot changed.
Coverage remains418/533, not419. The all-jet goal is incomplete; no clean-HEAD
reproduction is claimed for the dirty main tree.

## Verification

The complete module compiled with pinned Coq8.17.1 / CompCert3.14. Fresh
checker42165 exited0 after explicitly recompiling it, printing all4 result types
and4 definitions without elision, regenerating the Elements AST and recursively
kernel-checking the dependency chain. Independent evidence review18883 exited0
with35 deliberate proof/evidence corruptions rejected. A separate terminal
postcheck revalidates the receipt/log/tool hashes, fresh source/object identities
and unchanged main inputs before committing.

Expected dependencies: two closed footprint/count results, one specialization
result using the four inherited classical/extensionality assumptions, and one
complete-call/state result using the six inherited Coq/CompCert assumptions.
No new assumption, admission or unchecked operation is used. The isolated
`whole_c_endpoints=1` is not normal registration, coverage or full acceptance.

Development corrections were rewriting the existing `Zlength_correct` bridge,
using only list constructors instead of recursively constructing the contained
separation proposition, and following the already-destructed lookup/parser
goal rather than rewriting a lookup no longer present. No representation or
theorem domain was weakened to bypass a proof obligation.
