# Elements inputs_hash: reuse the three component programs

`source/jet_elements_inputs_hash_program.v.source` proves the original
`f_simplicity_inputs_hash` C getter against the literal Elements composition:
initialize SHA, absorb the outpoints and sequences digests, absorb the annexes
digest, and finalize. It reuses the checked component program semantics and
generic C getter execution proof rather than adding new primitives or an
execution/output premise.

Fresh compilation and complete type/definition/assumption reports passed:
