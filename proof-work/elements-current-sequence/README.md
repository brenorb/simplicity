# Elements current-sequence C-to-program bridge

The actual `simplicity_current_sequence` C jet has a checked local contract
against the literal program `primitive CurrentIndex >>> assert (primitive
InputSequence)`. Its interpretation uses the reviewed Haskell `toWord32` and
`fromWord32` algorithms, including the optional indexed lookup and assertion
failure branch. The source correspondence check follows the jet catalog,
transaction library, current-index primitive and literal assertion combinators.

The final theorem retains the original `application_jet_local_spec`:
`f_simplicity_current_sequence`, `elements_ge`, `Elements.env`, the exact
`current_scalar_rep` (544-byte input records, sequence at 248, input pointer at
0 and count at 696), and the complete execution/output/prefix/cursor/memory
postcondition. It does not assume the concluded execution or output. The
logical environment carries the existing current-index validity bounds; the
initial memory must represent that environment and valid frames. This is not
an unconditional claim about arbitrary bytes or invalid C environments.

## Shared structure

`elements_current_literal_sem` factors the current-index conversion followed
by assertion for **any** per-input primitive result type. It takes a proved
pointwise bridge for that primitive, not an execution/output premise. The
sequence instance discharges it with the previously checked
`elements_input_sequence_literal_matches`, then transports the existing full
C contract using `application_jet_local_spec_pointwise`. Other current-input
families can reuse this structure after proving their own literal primitive
and representation bridges. No other family is certified by this batch.

The three new results are the generic composition lemma, the sequence
interpretation bridge, and the actual-C local contract. The final dependency
set equals that of `elements_current_sequence_local_spec`: six inherited
assumptions, with no new libc model or proof shortcut. The interpretation
lemmas use inherited functional extensionality through the shared word
converter. The source archive is
`source/jet_elements_current_sequence_literal.v.source`.

## Checked evidence

The source guard reuses the InputSequence review and adds 22 in-memory
corruptions covering dispatch, primitive, current index, assertion direction,
literal word width, C function, logical environment, representation offsets
and vacuous whole-contract premises. Invalid proof text is never compiled.
Fifteen separate scope/source/object/assumption/terminal-evidence corruption
fixtures check the sealed receipt.

## Remaining integration

No main Coq source, build manifest, public registry, snapshot or compiled object
was installed. This batch adds **zero registered coverage**; it is isolated
checked implementation-to-specification progress, not normal acceptance.
After the running count admission terminates, integrate the input/current
literal modules under their final `C` namespaces, include the unchanged current
execution dependency closure, review all registry/snapshot deltas, add the
selected source guards to normal acceptance, and run full acceptance without
update/skip flags. Recompile after rebasing namespaces; an external `.vo` is
not a normal `C` module. Complete Elements environment-builder/evaluator
composition remains separate, as does every other uncovered jet.
