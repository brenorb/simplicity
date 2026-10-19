# Original field multiplier: through the second output store

`exec_original_fourth_integer_checkpoint` executes the first 82 original
statement heads of `f_secp256k1_fe_mul_inner`, through `r[1]` and the following
52-bit shift. Both statement-splitting equalities are checked against the
unchanged Clight body. The slice starts from the derived post-`r[0]`
checkpoint, not fresh memory or the old input array.

The proof returns an updated instance of the same `checkpoint_state`, with
original cached inputs kept separate from stored outputs. Loads of both
outputs are established in the current post-store memory: `r[0]` is preserved
and `r[1]` has the newly computed value. The `c`/`d` representation, live
temporaries and outside-original-footprint framing are retained.

The integer bridge reuses `accumulate_exact` and `products56_bound` for the
two low-column and three high-column products. Under the explicit
implementation limb bounds, intermediate accumulations fit in 128 bits.
The shifted `c` is below `2^63`, shifted `d` below `2^62`, and stored `r[1]`
below `2^52`; their exact values are derived, not new execution premises.

The initial prototype selected too many statement heads. Inspecting the
actual normalized statement tree showed that this included the next
accumulation after the `r[1]` shift. The failed representation equality
rejected that proposed boundary. The corrected, checked boundary is 82,
not 85. Production C and the proof target were not changed.

## Evidence and scope

Four sources, 40 results and 36 definitions. The exact expected profile is
35 closed results, two representation/load lemmas with four inherited classical
dependencies, and three execution results with the six inherited
Coq/CompCert dependencies. `RUN.json` records fresh compilation and full
type/definition/assumption reports; `CHECKED.json` additionally records
successful recursive kernel verification. A launch file is not success.

The first audit rejected the predicted assumption profile: the output-load
lemma is not closed, because the existing `C.jet_sx_rep.region_load` and
`rep_region` already carry the same four inherited dependencies. Direct
`Print Assumptions` confirmed this origin. No axiom or proof was changed.
`verify-initial-profile.py.source`, `initial-profile-assumptions.log`, and
the original launch files preserve that failed audit. `RECHECK-LAUNCH.json`
starts the corrected exact-profile check; only its completed `RUN.json` and
subsequent kernel receipt are successful evidence.

Audit tree: `/private/tmp/jet-field-checkpoint-audit.Zeze9g`, sources in
`fourth/` under namespace `FieldFourth`. The parent binds 95 previously
forcibly rebuilt local imports and 26 checked extension modules. All loaded
source/object provenance is checked before and after verification.

```sh
python3 -B proof-work/secp-field-fourth/verify.py compile \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-fourth/verify.py kernel \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
```

This is partial helper execution, not full jet equivalence; coverage added
is zero. Remaining multiplication stages, final field-product bridge,
function entry and jet reader/writer/lifecycle composition remain open.
The caller must still establish the implementation limb bounds. No
production C, original specification, API, generation configuration, main
proof source or registry is changed.

Next: instantiate the returned checkpoint for the slice ending with `r[2]`.
Inspect its boundary in the generated statement tree. Keep the cached
original inputs fixed while updating the stored-output function after each
store, and continue reusing the checked accumulation, mask and shift lemmas.
