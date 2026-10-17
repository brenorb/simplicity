# Issuance: construct initial premises, then execute original C

Source-binding follow-up: this chain does not load the stale Bitcoin module
found during integration review. A separate forced rebuild of its complete
local dependency closure is in `../elements-issuance-clean/`. Keep the receipts
here for their exact compiled inputs; incremental make is not by itself a
full source/object correspondence check.

This companion strengthens the non-vacuity evidence for the original-C
equivalence in `../elements-issuance-status/`. It adds six complete results,
including `elements_issuance_status_runs_everywhere` in
`source/jet_elements_issuance_status_constructible.v.source`.

For every logical Word32 input and Elements environment it constructs a C
memory, environment value and valid frames, executes the unchanged
`f_simplicity_issuance`, and obtains the canonical three-cell encoded result.
No memory, frame, environment-representation, cached-hash or execution premise
is supplied at that final boundary. The unrestricted arbitrary-frame local
theorem remains the authoritative preservation contract; this companion is
an existential constructed-memory execution witness, not a replacement for it.

The construction uses existing verified allocation/store, array/environment
and frame-construction lemmas. It writes the actual issuance enum at offset
528 in each 544-byte input record, represents the input pointer/count and
environment pointer, proves stability under fresh-frame extension, then
applies the checked local theorem. All input indices and the three issuance
tags are covered. This is not a proof about the production malloc builder or
overlapping stand-alone API buffers.

`RUN.json` binds a fresh dependency rebuild and full reports for all 22 results
and 17 definitions in this six-module chain (the five unchanged archived
modules from `elements-issuance-status` plus this companion). Exact assumption
inventories distinguish six closed results, one reader-semantic result using
functional extensionality, six CompCert memory/expression results using four
inherited dependencies, and nine execution results using the existing six.
There is no new axiom, admitted proof or unchecked cast.

```sh
python3 -B proof-work/elements-issuance-constructible/verify.py compile PRIVATE_TREE
python3 -B proof-work/elements-issuance-constructible/verify.py kernel PRIVATE_TREE
```

Use a distinct private current-source clone containing the exact six archives
as `.v` files. Existing manifests are preserved; unregistered proof dependencies
are added to the makefile command line, with unchanged project load paths.
The once-only kernel launch is recorded in `KERNEL-RUN.json`. `CHECKED.json`,
when present, records successful recursive checking and postchecks for its
exact source/object identities. Do not infer success from a launch alone or
overwrite a receipt. Normal registration/full acceptance and coverage are
separate; this package adds zero registry entries.
