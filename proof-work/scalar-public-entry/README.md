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

Next: assemble the public original call nodes with those two checked helpers;
preserve the copied source and frame invariant during the zero helper; write
the canonical bit, return true and free both locals. Then perform normal full
acceptance before registration. Main checkout public coverage remains 351/533;
this archive adds zero. All work is local; Claude retains memcpy/SHA scope.
