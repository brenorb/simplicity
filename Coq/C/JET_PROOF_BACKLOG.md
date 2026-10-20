# Remaining jet proof work

The current local-contract registry contains 430 of the 533 header declarations.
The ten recently completed registrations and their conditions are listed in
[JET_ACCEPTANCE.md](JET_ACCEPTANCE.md); 103 declarations remain unregistered.

The remaining work includes:

- shared frame-domain and evaluator admissibility;
- exhaustive inherited correspondence to canonical programs;
- general caller startup and persistent SHA/global-state readiness;
- libc implementation proofs where a contract assumes `memcpy_model`;
- raw transaction/taproot projections for cached Bitcoin environment fields.

[JET_INHERITED_REVIEW.md](JET_INHERITED_REVIEW.md),
[JET_FIDELITY_REVIEW.md](JET_FIDELITY_REVIEW.md) and the `JET_*_MISMATCHES.md`
reports describe these boundaries. Production C, canonical Haskell and the
frozen `Coq/Simplicity` model must not be changed to make a proof pass.

Unique earlier candidates, diagnostic witnesses, derived trees and the parallel
field multiplication/square alternative remain in `../../proof-work/`, outside
the active build. See its README for recovery instructions and archive limits.
Their presence does not register or accept additional jets. Current acceptance
is reproduced with `bash Coq/check-jets.sh --accept`; old run records and
continuation journals are not required.

## Current target: `simplicity_gej_rescale`

The separate-output square support is now in the ordinary
`jet_secp_square_separate_{layout,exec,numeric,caller}.v` modules. It executes
the original helper into an uninitialized, distinct destination, preserves
the input and allocation permissions, and reuses the selected square proof's
arithmetic and literal-specification bridge. It is not a second registration
of `fe_square`.

`jet_secp_rescale_prefix.v` proves execution of the first two statements of
the actual helper body: the retained `fe_is_zero` check loop and the square
into local `zz`. The numeric endpoint preserves the scalar field, the point's
128-byte allocation permissions and `zz`'s 40-byte allocation permissions,
and supplies the square value and reusable limb bounds. There is no nonzero
scale premise. These are prefix/helper results, not a completed jet contract;
coverage remains 430/533.

With the documented Coq 8.17.1 toolchain and matching pinned dependencies,
reproduce the focused build and recursive kernel check with:

```sh
JET_TARGETS=C/jet_secp_rescale_prefix.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -silent -o C.jet_secp_rescale_prefix
```

Next discharge actual entry/allocation, the four multiplications and their
preservation facts, then compose the public reader/writer lifecycle with the
literal `gej_rescale` program. Coordinates live at offsets 0, 40 and 80 inside
one owned 128-byte point allocation. The existing owned multiply contract
requires each owned region's base to be zero; it cannot directly represent
a fictitious 40-byte allocation at offset 40 or 80. Reuse the whole-point
region pattern in `jet_secp_point_write_run.v` when extending execution
support. Claude's checked u128 helper oracles remain available in the
parallel-proof archive if needed; do not register the alternative
`fe_multiply` or `fe_square` endpoints as well as the selected ones.
