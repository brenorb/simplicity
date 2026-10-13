# Reviewed shared foundations integration — first batch

This is an additive integration of Claude's frozen local commit
`30404face45383153528f36d915de6d7df11f3f4` into `feat/jet-equivalence`.
The ten imported modules are byte-identical to that commit. The eleventh is
our previously reviewed raw tappath adapter, with only its `NullableC` import
changed to `C`. There is no production C, generated-program, canonical
specification, existing proof, or registry change.

## Scope

- `jet_frame_constructible`: arbitrary encoded input and writable output
  frames on fresh blocks, preserving loads on existing blocks.
- `jet_frame_constructible_bm`: representation, separation and writable
  output for every Bit Machine state within explicit addressability bounds.
- `jet_frame_constructible_context` / `_jets` / `_app`: compose those
  constructions with the existing complete execution contracts. Generic
  helper premises about a jet's local specification are not new jet proofs.
  Application helpers still require a represented logical environment.
- `jet_env_constructible{,_array,_array_x,_ext}`: reusable record/array
  construction and memory-extension preservation. These are CompCert memory
  constructions, not proofs that the actual C environment builders execute.
- `jet_bitcoin_tappath_nullable{,_raw}`: complete original tappath C execution
  against the existing primitive/raw projection, with the path pointer
  required only when the path is nonempty. Old environments remain supported;
  the nonempty relation is unchanged. Empty-path and NULL boundary lemmas
  accompany the result. The inherited raw path-length bound of 128 remains.

Neither general frame construction nor the empty-path lemmas restrict the
existing registered contracts to fresh frames or zero output contents. The
construction chooses convenient witnesses; it does not change their domain.

## Verification and build access

`manifest.json` pins all 11 source modules, 91 results and 33 definitions.
`check.py --build` recompiles the modules in normal `C` namespaces, prints
every result's assumptions and full types/definitions, then independently
kernel-checks the entire dependency chains. Its isolated base is the completed
scalar-lambda acceptance tree (session 21530, terminal exit 0), fingerprint
`0272f0370fbe4a3b6dd73aa21688bc52e0bfd494cbf1c292bf3f12ae85d68616`.
All inherited proof sources also present in this checkout must agree with
that base. The checker refuses imported source drift and proof escape commands.

```sh
ulimit -s 65520
python3 -B proof-work/shared-foundations-integration/check.py --build
python3 -B proof-work/shared-foundations-integration/check.py
python3 -B proof-work/shared-foundations-integration/test-check.py
```

The build prints a receipt; persist it as `REVIEW.json` only after checking
terminal success. The read-only default checks the pinned sources, objects,
driver and logs against that receipt. Scratch evidence remains local in the
recorded temporary directory. The inherited compiler is Coq 8.17.1,
CompCert 3.14 and VST 2.14; an available pinned compiler is used explicitly.

Recorded run `/tmp/jet-shared-foundations.nvgogeyq`: all 11 fresh module
compilations, the full audit driver and the independent kernel exited 0.
All 91 results and 33 definitions were printed without truncation; 27 results
are closed, the others retain exactly four or six inherited dependencies.
The 15-name library kernel context is unchanged and all three unsafe
categories are empty. Thirteen read-only negative evidence fixtures pass.

This is a separately checked support batch, not normal registry admission or
whole-jet acceptance. The default jet build does not yet select these modules;
the command above is their explicit verification target. No jet is added to
the coverage count, and the old registered tappath theorem is retained.

## Next reviewed batches

1. Admit the nullable raw theorem for the existing tappath coverage row in an
   isolated reconciled registry candidate, reviewing the exact contract and
   axiom changes before full acceptance. This strengthens its domain, not
   the number of jets. Preserve the old relation for compatibility.
2. Add the Bitcoin environment stability/constructibility consumers and
   per-jet executability instances, refreshing the old 349-jet inventory
   against our current registry. Reuse these foundations rather than copy
   another private frame constructor.
3. Independently verify SHA startup and real Bitcoin caller/builder chains;
   retain their startup, readable-memory and explicit library boundaries.
4. Keep linked reference-library programs separate from the original
   external-library programs. Replace the three unchecked linking casts
   before admitting that batch. Do not silently remove `memcpy_model`.
5. Review Elements semantics beyond the already checked Version clause,
   include its actual AST regeneration gate, and leave unfinished C helpers,
   sorting and builder work outside equivalence coverage.

The sibling worktree and its ongoing untracked copyInput experiment are
untouched. Existing main index/worktree changes are preserved. This batch
does not resume or complete the paused app goal. Local signed commits only;
never push.
