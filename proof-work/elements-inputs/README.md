# Elements inputs_hash: reuse the three component programs

Private tree: `/private/tmp/jet-elements-inputs.emQfCi1J`, cloned from the
completed outpoints proof tree, not from a live audit. Main inputs and the
original staged patch remain unchanged.

`source/jet_elements_inputs_hash_program.v.source` proves the original
`f_simplicity_inputs_hash` C getter against the literal Elements composition:
initialize SHA, absorb the outpoints and sequences digests, absorb the annexes
digest, and finalize. It reuses the checked component program semantics and
generic C getter execution proof rather than adding new primitives or an
execution/output premise.

Fresh compilation and complete type/definition/assumption reports passed:

```sh
python3 -B proof-work/elements-inputs/check.py /private/tmp/jet-elements-inputs.emQfCi1J
```

`RUN.json` binds three results and two definitions. Parametricity is closed;
the pure semantic bridge uses inherited functional extensionality; the C
endpoint has exactly the six inherited assumptions. Its explicit separated
cache/frame relation places the computed raw digest at transaction offset440
in the760-byte transaction structure. Actual caller cache construction and
formal host-library equivalence are not claimed.

Recursive kernel/AST verification and canonical-source/evidence review remain.
This unregistered proof does not change accepted coverage or establish full
normal acceptance or completion of the every-jet goal.
