# Scalar reader/zero continuation

This archive continues the preserved scalar-u128 work without changing its
historical sources or namespace. The current 23 helper modules have 86 actual
completed Lemma/Theorem declarations and fresh compilation on Coq 8.17.1,
CompCert 3.14 and the current selected C.jets_secp AST. Two small export wrappers
resolve the old OriginalC dependencies to their checked C counterparts; they
introduce no definitions, premises or proof results.

The two new/changed proof sources here are the corrected overflow Boolean
interpretation and the new original-C overflow-to-group-order bridge. All
other 21 sources are reused by exact hash from ../scalar-u128, not duplicated.
The flags correction first collapses machine ORs before matching AND/NOT on
Boolean bits; the previous one-shot rewrite order missed those nested forms.
The numeric bridge handles arbitrary four int64 limbs. It derives the actual
helper call's return flag from representation and discharged machine bounds;
it does not assume a correct flag or replace the public jet specification.

Four-module independent kernel checking 32260 exited 0 (twelve imported context
axioms, empty unsafe categories). Full 23-module checking **44992 exited 0**
with fifteen inherited imported context axioms and empty unsafe categories.
The 86-result Print Assumptions run **8576 exited 0**. Strict review found 57
closed results and exactly six inherited execution assumptions in the union;
the new overflow flag bound is closed, and its Clight execution theorem has
exactly those six assumptions. ASSUMPTION-REVIEW.json records every set.
All 23 actual source hashes/declaration inventories match the archive. Completed kernel
checking of these helpers still is not public scalar equivalence or coverage.

Reproducible scratch load path, from the independent normal candidate Coq dir:

```sh
export PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH
ulimit -S -s 65520
bash build-jets.sh --coqc -R /tmp/jet-scalar-reverify.8hswEF OriginalC \
  /tmp/jet-scalar-reverify.8hswEF/jet_secp_scalar_overflow_numeric.v
```

The final checked declaration is eval_scalar_overflow_numeric. Two earlier
failed new-module compilations were notation/import mismatches after the
numeric flag proof, not successful completion of the module. Only the final
86360 exit-0 run counts. The incomplete flags-debug.v was used with coqtop Show
only and is neither archived proof input nor a compiled result.

Next work is driven by the intended public scalar_is_zero theorem:

1. Finish independent kernel/per-result reviews; review every helper type and
   contract definition, especially external-model/NULL branch/ownership scope.
2. Derive scalar_set_b32's current output limb value as the input modulo the
   group order. It already executes the real overflow and reduce calls; do not
   add correct-output, overflow or successful-copy premises to the public result.
3. Prove read_scalar's real byte-buffer allocation, secp_read8s_layout call,
   scalar_set_b32 NULL call and free. The current secp_frame module already
   transports read8s to the correct secp environment: reuse that theorem.
4. Compose read_scalar, scalar_is_zero and the real writeBit call with full
   public entry/source-copy/return/local-free/framing. Reuse the actual-size
   owned public lifecycle helpers where their interfaces fit.
5. Bind the public result to literal canonical Simplicity scalar_is_zero,
   including its raw group-order-equality branch; add parametricity/source gates,
   complete audit inventories and isolated normal-build/full acceptance.

No public entry, accepted coverage or new mathematical-only goal is claimed.
Step 1 is now completed: contract generation 26431 exited 0, and all 86 types/
64 definitions plus every dependency set are reviewed. CONTRACT-REVIEW.json/.md,
review-contracts.py and its fixtures record/reproduce the result. Step 2 remains
the current proof obligation; keep the literal public end-to-end theorem in view.
Its reduction-value component is now checked in `../scalar-reduce`: 20 further
results (18 closed), all 20 types/17 definitions reviewed, independent kernel
session 56508 exit 0. The final internal theorem executes actual scalar_reduce
and exposes current output loads, modulo-group-order value, return and framing.
The caller must derive its overflow flag from the real classifier. Byte assembly
and scalar_set_b32 composition remain open; these results do not add public scalar
coverage. The scalar-next sources and 86-result review inventories are unchanged.
Point acceptance **77601 exited 0**. Affine generation **90113 exited 0** and
its complete snapshot review passed; full affine acceptance **13065 is live**
in the frozen derived candidate. This scratch does not change those inputs.
