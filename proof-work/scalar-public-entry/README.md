# Actual scalar-zero public entry and local storage

Seven compiled and independently kernel-checked internal results support the
unchanged `f_simplicity_scalar_is_zero` caller. The concrete entry uses actual
16-byte frame and 32-byte scalar allocations, actual parameter binding and
the generated undefined flag temporary. Its environment uses the scalar's
actual `__5826` composite, not the field or point composite.

The reader's initial two-region invariant is derived from ordinary Freeable
storage, source-frame fields and block separation. No initialized scalar-cell
values are assumed. The copy lemma executes the actual by-value 16-byte source
assignment from its concrete loadbytes/storebytes facts. The release lemma
derives actual `Mem.free_list` and preservation outside both locals from their
retained Freeable permissions; local release is not assumed.

These are **support lemmas**, not complete public jet equivalence. The final
caller still must produce its allocations and copy store, derive frame
invariants, compose read/test/writeBit/return and invoke the release proof.
No call, desired output, write or free premise may remain in that public result.
The entry/copy/storage/free contracts are conditional building blocks to be
discharged by that composition, not new public assumptions.

Compiler session 23053, seven-type/two-definition untruncated contract driver,
assumptions session 99934 and independent kernel session 30315 all exited 0.
Three results are closed; three use four inherited classical/extensionality
assumptions; actual statement copy execution additionally uses CompCert's two
execution-semantic parameters. Kernel context: 15 inherited axioms, all three
unsafe categories empty. The manifest and reviewer pin current sources,
drivers and output hashes and check each exact per-result dependency set.
Eight in-memory negative fixtures reject evidence drift without touching inputs.

```sh
python3 proof-work/scalar-public-entry/review.py --work /tmp/jet-scalar-reverify.8hswEF
python3 proof-work/scalar-public-entry/test-review.py /tmp/jet-scalar-reverify.8hswEF
```

Sources are `.source` archives outside accepted load paths. Reproduce with
pinned Coq 8.17.1, stack 65520 KiB, cwd
`/tmp/jet-ge-negate-accept.5mtyZa/Coq`, and narrow
`-R /tmp/jet-scalar-reverify.8hswEF OriginalC`. The exact kernel command is
in the manifest. Read lifecycle and literal-zero bridges are independently
checked in `../scalar-reader-lifecycle` and `../scalar-reader-zero`.

Next: assemble the public original call nodes with those two checked helpers;
preserve the copied source and frame invariant during the zero helper; write
the canonical bit, return true and free both locals. Then perform normal full
acceptance before registration. Main checkout public coverage remains 351/533;
this archive adds zero. All work is local; Claude retains memcpy/SHA scope.
