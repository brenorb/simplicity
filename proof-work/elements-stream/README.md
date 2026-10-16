# Shared hash-word semantics and Elements stream getters

Private tree: `/private/tmp/jet-elements-stream.1zVQb2CU`.
Its source/object seed is the completed fully accepted combined420 candidate,
not either currently running audit's mutable object cache. Main proof inputs
and the original staged patch remain untouched.

## First completed checkpoint

`C.jet_sha_hash_words_reader` freshly compiled and its15 results / one
definition were reported completely by:

```sh
python3 -B proof-work/elements-stream/check-reader.py /private/tmp/jet-elements-stream.1zVQb2CU
```

`READER-CHECKED.json` binds the exact archived source, fresh object, commands,
full reports, assumption sets and preserved main/index state. It is a
development checkpoint, **not** recursive kernel success or C-jet coverage.

The helper generalizes only the environment-dependent evaluation layer of
the existing literal `hashLoop` / `hash_words_spec` programs. It reuses the
already checked generic `for_while_program_reader_sem`, traversal theorems,
`loop_step`, `loop_prefix_some`, finite-counter bounds, SHA context absorption
and finalization. It handles empty arrays and both early-stop/counter-full
paths for arbitrary widths and environments, without a new primitive
signature, artificial Bitcoin environment witness or assumed hash oracle.

The exported interface is `hash_words_reader_sem`. The remaining target is
to instantiate it with the actual Elements primitive semantics and compose
the existing complete `elements_hash_getter_writeHash_local` execution proof
for output scripts/range proofs/surjection proofs, input scripts/sequences/
scriptSigs and tappath. Cached-memory representation obligations must remain
explicit and tied to those raw-data programs. No C endpoint is claimed yet.
