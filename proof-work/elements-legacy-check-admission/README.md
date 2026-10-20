# Legacy Elements lock assertions: normal-registration candidate

Proposed successor: **406/533**, adding only the two original-C
`broken_do_not_use_check_lock_{distance,duration}` jets after the reviewed404
candidate. Main is **401/533**, not406. This candidate is not installed and has
not passed full normal acceptance.

Only completed private proof objects were cloned from the independently
kernel-checked assertion tree. The reviewed404 predecessor supplied source
text, never objects from a live acceptance audit. Main and its original staged
patch remain unchanged by assembly, preparation and review.

## Proof and exact registration scope

One new module, `C.jet_elements_legacy_check`, contributes eight results and
five definitions. Its whole-C partial contracts derive both C return cases,
read/helper/comparison execution, frame/cursor/prefix behavior and memory
preservation. Three results are closed. Both concrete endpoints retain exactly
the six inherited assumptions. See `../elements-legacy-check/` for full proofs,
kernel/AST reports and canonical source/evidence review.

The initial logical/cache representation relation stays explicit; caller cache
construction is not proved by this batch. No desired success, helper execution,
or output is assumed. LP64/RECKLESS and host-library boundaries are unchanged.
The full every-jet goal remains unfinished, including the unchanged104 explicit
`memcpy_model` conditions and all remaining missing jets/shared obligations.

There are two mandatory source/negative guards, an exact partial-contract
coverage case, and fourteen new statement-confined coverage corruptions. In
particular, replacing the assertion/failure contract by a total getter contract
must be rejected. The inherited total-getter fixtures remain byte-identical.
Review caught and corrected a copied fixture's contract-kind mismatch before
running tests; no proof statement or assumption was changed. The repeated
fixture blocks required unique long patch context to preserve the old block.

## Completed preparation and independent finish review

This batch reuses `normal-delta-prepare.py` unchanged. The immutable v1 review
engine remains byte-identical for earlier pending audits. Its new version,
`normal-delta-review-v2.py`, retains the same substantive delta/evidence checks
but delegates recognition of historical main input maps to the batch's exact
checkpoint resolver. This is needed because this candidate was prepared at
main401 while404 was itself prepared at399. Unknown maps still raise an error;
there is no permission for arbitrary main drift or mutation of predecessor
configuration. The source/evidence tests include an unrecognized input-map
corruption.

The six-stage finish review was launched once as **31051** and terminated with
exit0:

No full406 audit or installation has been launched. They must follow the real
predecessor acceptance/installation chain, not a prepared snapshot or launch
record. Main401 audit **92989** and isolated402 audit **26900** are live; keep
their semantic inputs frozen. The combined407 plan now supersedes the earlier
serial402/404/406 installation sequence: this reviewed delta is included
unchanged, and the combined audit checks all407 entries over installed401.
Keep main at401 until actual-main401 and combined407 both pass; do not install
intermediate candidates. See `../elements-output-nonce-admission/README.md`.
Scoped signed
commits go only to the brenorb fork, preserving unrelated dirty registries and
the entire original index.
