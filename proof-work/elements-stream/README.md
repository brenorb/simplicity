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
full reports, assumption sets and preserved main/index state. Two results are
closed; the other13 have only the existing dependent-functional-extensionality
principle through the Reader dictionaries. This is a development checkpoint,
**not** recursive kernel success or C-jet coverage.

The helper generalizes only the environment-dependent evaluation layer of
the existing literal `hashLoop` / `hash_words_spec` programs. It reuses the
already checked generic `for_while_program_reader_sem`, traversal theorems,
`loop_step`, `loop_prefix_some`, finite-counter bounds, SHA context absorption
and finalization. It handles empty arrays and both early-stop/counter-full
paths for arbitrary widths and environments, without a new primitive
signature, artificial Bitcoin environment witness or assumed hash oracle.

The exported interface is `hash_words_reader_sem`.

## Seven complete C endpoints now compiled and reported

`C.jet_elements_words_hash_program` instantiates that interface with the actual
Elements primitive algebra. It proves the whole original C getters against
the same literal hash-word programs for output scripts/range proofs/surjection
proofs, input scripts/sequences/scriptSigs and tappath. Each endpoint composes
the existing complete `elements_hash_getter_writeHash_local` execution proof,
including original function/body, linked global environment, field layout,
separated frame/output/prefix/load guarantees and all cursor positions covered
by that contract. No desired execution or output fact is added as a premise.

The cached-memory representation remains explicit: it requires each field to
contain the hash determined by the represented raw scripts, proof bytes,
sequences or path. This does **not** prove the actual C environment builders
populate those fields. Confidential proofs retain the existing raw-byte
primitive interpretation; no arbitrary independent digest input replaces it.

Fresh compilation/reporting completed with exit zero (handle12829):

```sh
python3 -B proof-work/elements-stream/check.py compile /private/tmp/jet-elements-stream.1zVQb2CU
```

Both new modules and both reused C getter-helper modules compiled freshly.
`RUN.json` binds all36 results /10 definitions, including13 closed results and
exactly six inherited assumptions for each of the seven whole-C endpoints.
No assumption allowlist changes or admissions are introduced. Source archives
are exact, including raw printer whitespace in the evidence logs.

The separate once-only recursive kernel phase completed with exit zero
(handle47464), including Elements AST regeneration:

```sh
python3 -B proof-work/elements-stream/check.py kernel /private/tmp/jet-elements-stream.1zVQb2CU
```

It checked Elements AST regeneration and the recursive two-module closure.
Its private input fingerprint is
`1ea5fc98311d57d465913a6ddf9c7587dce5875193f0dcd161d148219da354cd`.
`CHECKED.json`, `ast.log` and `kernel.log` record the actual terminal result.
The kernel context reports no type-in-type, unsafe fixpoints or assumed
positivity. The endpoint-specific assumption reports remain exactly six
inherited assumptions each; the wider imported kernel context is separate.
Do not restart this completed kernel phase or alter its bound source/tools.

The separate selected canonical source review also completed, with203
read-only corruptions rejected; its exact scope and receipt are in
`../elements-stream-source/`. It establishes selected source correspondence,
not formal host-runtime equivalence or C cache-builder correctness.

Next: independently bind the complete proof/kernel/source evidence, then
normal registration/review/full acceptance over the eventual accepted436
successor. No normal coverage, full acceptance or all-caller construction
result is claimed by this development checkpoint.
