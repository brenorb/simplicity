# Elements input_annexes_hash: original C against the primitive program

Private tree: `/private/tmp/jet-elements-annex.sihNn4TS`.
Object/source seed: the completed, kernel/source/evidence-reviewed seven-jet
Elements proof tree `/private/tmp/jet-elements-stream.1zVQb2CU`.
No running audit's objects were copied and no main Coq source was changed.

Two new modules are archived under `source/`:

- `C.jet_sha_hash_elems_reader`: the existing literal element-absorbing loop
  and initialization/finalization program over **any** option Reader. Reuses
  `gen_prefix_some`, `gen_step`, the counter traversal proofs and the checked
  SHA absorption/finalization results. It does not introduce a primitive.
- `C.jet_elements_annexes_hash_program`: the Elements `InputAnnexHash` primitive
  over raw annex bytes, the literal loop using the existing `annex_hash_spec`,
  and `elements_input_annexes_hash_program_local_spec`. The final theorem
  executes `f_simplicity_input_annexes_hash` in `elements_ge` and relates its
  output to that original primitive program.

The option cases stay distinct: an absent annex absorbs the zero marker;
a present annex, including empty bytes, absorbs the one marker and its SHA-256
digest. The 32-bit iteration bound and SHA context bound are discharged.

Fresh compilation and full declaration/assumption reports succeeded:

```sh
python3 -B proof-work/elements-annexes/check.py compile /private/tmp/jet-elements-annex.sihNn4TS
```

`RUN.json` and its exact logs record all nine results and four definitions.
The public C endpoint has exactly the six inherited assumptions; no new
assumed declaration, disabled kernel check or desired-execution premise.

The recursive-kernel phase completed with exit zero using:

```sh
python3 -B proof-work/elements-annexes/check.py kernel /private/tmp/jet-elements-annex.sihNn4TS
```

`CHECKED.json`, `KERNEL-RUN.json`, `kernel.log` and `ast.log` bind the successful
recursive kernel and Elements AST-regeneration results. The candidate source
fingerprint is
`d9526f804b5c9d67cd9f55e900a686d9ca85cdfa3402e2a4a3e27d9aaff656ae`.
Canonical source review and63 read-only mutation tests also passed, recorded
separately in `../elements-annexes-source/`. Independent evidence review is
running; normal registration still remains. This is not an accepted coverage
addition or a full normal acceptance result.

The environment relation remains explicit: the actual cached transaction
field at offset 376 is represented by the computed raw-annex program hash,
with the usual readable/disjoint frame premises. This endpoint does not prove
that an actual transaction constructor establishes that cache relation.
Host-library equivalence is not claimed. The broader every-jet goal remains.
