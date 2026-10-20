# Three asset getters: reviewed normal410 candidate

Proposed successor: **410/533**, adding input_asset, output_asset and
current_asset after the reviewed407 source candidate. Main is still401/533.
This candidate is not installed or fully accepted.

The three whole-C contracts are documented in `../elements-asset-literal/`.
They retain actual C execution, original memory/frame relations, arbitrary
output contents, prefixes/cursors and framing. The confidential encoder reuses
the native packed-word projection and is polymorphic in the explicit payload.
Three pure lemmas are closed. Each concrete C endpoint has exactly the six
inherited assumptions, without a new libc or execution/output premise. Caller
construction, the inherited empty-array pointer domain, host-library/fidelity
boundaries and LP64/RECKLESS remain explicit; no field-arithmetic proof is
claimed or substituted for implementation equivalence.

## Completed preparation and independent review

The normal build and explicit fresh module compilation passed as99733, exit0.
One new module contributes nine results and six definitions. All **8,439
inherited contract records** preserve bytes/order, and all **5,541 inherited
dependency sets** are unchanged. All fifteen added records have complete deep
reports, with no compact elision supplements needed. Shared preparation and
checkpoint-aware review engines are reused unchanged.

## Next integration boundary

Do not alter the live407 candidate to include these proofs. Keep main401 and
audits92989/26900/23810 frozen. Combined407 installation requires both real
actual-main401 and isolated407 success, preserving the exact source-only delta
and original index; see `../elements-output-nonce-admission/README.md` and its
read-only28-target installation plan. No intermediate402/404/406 installation
is needed under that combined plan.

After guarded407 installation, this successor can undergo full acceptance
alongside actual-main407. Alternatively, include the separately completed
amount-family proofs in a new413 source candidate and fully audit that combined
successor; retain the reviewed410 delta unchanged. No410/413 full audit or
installation has been launched, and no407 installer is yet implemented.

This proposed410 registry retains104 explicit `memcpy_model` conditions and123
missing public declarations. The full every-jet goal and shared caller/domain,
evaluator/library/fidelity/configuration obligations remain unfinished. The
receipts bind the actual dirty/staged base, not clean-HEAD reproducibility.
