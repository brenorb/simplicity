# Actual null-data call in a represented Bit Machine

Private tree: `/private/tmp/jet-null-data-bitmachine.GPJBlwNP`.
Fingerprint:
`4dc6ef131b2744a1b333c8950e23206637fd2cc51b1a03d56d4f0346f593b490`.
The new source is archived under `source/`; inherited sources equal the checked
`../elements-null-data-layout/` tree byte for byte. Main418 semantic inputs and
the original staged patch are unchanged.

## Stronger checked endpoint

`elements_output_null_datum_bitmachine` combines the complete actual C call
with the represented Bit Machine. From `bm_rep`, `bm_separated`, the usual
active-write permissions, canonical input cells at the front of the active read
frame, enough output capacity and the explicit C/environment correspondence,
it returns the canonical primitive result, actual CompCert call and `bm_rep`
of the state with that result written. The active read frame and every inactive
frame remain represented; existing earlier output cells are preserved.

The theorem no longer asks the caller to supply unread-input/output separation,
initial physical Word32 inputs, source-frame alignment/cursor facts, or a
writable output-frame layout. They are derived from the existing representation
and separation predicates. In particular:

- `bm_active_read_encoded_prefix` is a reusable lemma for an arbitrary Simplicity
  input type, not just this jet. It extracts a canonical input prefix, source
  header, alignment and cursor bounds from `bm_rep`.
- The existing canonical pair-encoding theorem gives both Word32 inputs.
- `bm_active_read_word_out_sep` establishes the actual unread-j word separation
  across the full261-bit output range. Input/output cells stay in the same
  allocation; arbitrary valid cursor positions and word crossings are supported.
- `write_frame_at_of_rep` derives the writable frame; `bm_rep_after_write` turns
  the complete call's output/prefix/public framing into preservation of the
  whole represented state.

The environment-case predicate contains **no input-frame separation premise**:
only the opcode-count/code/hash representations and their environment/output
footprint separation. Logical output/script lookup correspondence is explicit.
No desired C execution, output or final memory representation is assumed.

## What is still not accepted

The target remains the pinned assertion-disabled Elements program. This
unregistered theorem is not `application_jet_local_spec_sep`: it expressly
uses evaluator-valid Bit Machine frames. It does not prove unrestricted
overlapping-buffer correctness, that the C evaluator establishes/maintains the
representation invariant, or that real Elements environment builders establish
the opcode/parser/cache correspondence. The existing generic gap-buffer layout
theorem is relevant evidence for the separation discipline, not itself a proof
of invariant maintenance by the real evaluator.

Next package the environment case/lookup facts into a reusable environment
relation independent of the chosen input, review canonical Haskell/Coq-port
fidelity, and admit the exact contextual contract with its domain explicitly
recorded. Do not rename it as the broader old local contract or count it as an
installed jet before that review. Keep empty output arrays, non-null-data
scripts, missing indices and all22 datum constructors in scope. The separate
header/API aliasing question remains open; see
`../null-data-overlap-probe/README.md`.

No main C, header, primitive, registry or acceptance snapshot changed.
Registered coverage remains418/533 and the all-jet goal remains incomplete.
No clean-HEAD reproduction is claimed for the dirty main tree.

## Verification

The complete module compiled with pinned Coq8.17.1 / CompCert3.14. Fresh
checker16099 exited0 after explicitly recompiling it, printing both result
types and all3 definitions without elision, regenerating the Elements AST and
recursively kernel-checking the dependency chain. Independent evidence review
76107 exited0 with35 deliberate proof/evidence corruptions rejected. A separate
terminal postcheck revalidates its receipt/log/tool hashes, fresh source/object
identities and unchanged main inputs before committing.

Expected dependencies: the generic input-prefix lemma uses the four inherited
classical/extensionality assumptions; the complete-call/state theorem uses the
six inherited Coq/CompCert assumptions. No new axiom, admission or unchecked
operation was added. `whole_c_endpoints=1` records this explicit contextual
endpoint, not normal registration or added coverage.

```sh
python3 -B proof-work/elements-null-data-bitmachine/review.py /private/tmp/jet-null-data-bitmachine.GPJBlwNP
```

Development corrections: remove an unused layout binder from the cursor
definition, explicitly instantiate the dependent input type when passing a
pair, and normalize the output-capacity equality before record destruction.
The last change avoids broad reduction expanding a symbolic canonical output
inside arithmetic; the same frame/data invariant and theorem scope are retained.
