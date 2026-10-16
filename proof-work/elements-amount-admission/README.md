# Three amount getters: reviewed normal413 candidate

Proposed successor: **413/533**, adding input_amount, output_amount and
current_amount over the reviewed410 asset source candidate. Main remains
401/533; neither this candidate nor410 is installed or fully accepted.

Private tree: `/private/tmp/jet-amount-admission.ngvsw_yd`.
Input SHA-256:
`e63c5fcf9b50020ebacbbca7945731222b50ff0d34fdfbbf173c87223b6245c8`.
Only completed amount-proof objects were cloned. The reviewed410 predecessor
supplied source text, never objects from the live407 audit. Main, live audit
sources and the original staged patch remain unchanged.

The three whole-C contracts are documented in `../elements-amount-literal/`.
The canonical amount primitives return only confidential amounts, but the jet
programs pair them with assets and route asset first, amount second. The
correspondence guard checks that exact routing, unsigned Word64 conversion,
padding, original/transported statements, C bodies and memory relations. The
payload-polymorphic confidential encoder, generic list-index bridge and
current-input transport are reused. The two pure lemmas are closed; each C
endpoint retains exactly the six inherited assumptions. No new execution,
output, success, canonicality or libc premise is introduced.

## Completed preparation and independent review

Assembly58155 and preparation56873 terminated with exit0. The normal build
and explicit fresh compilation passed. One new module contributes eight
results and five definitions. All **8,454 inherited contract records** retain
bytes/order; all **5,550 inherited dependency sets** are unchanged. All thirteen
new records have complete deep reports, without compact elision supplements.
The shared preparation and checkpoint-aware review engines are unchanged.

Six-stage finish91142 terminated with exit0: coverage, coverage tests
(including21 new statement-confined corruptions), ordinary contract comparison,
canonical/source checks,71 source corruptions and31 independent normal-review
corruptions passed. `REVIEW.json` binds the commands, terminal logs, sources,
tools, both engines and fresh object/report evidence. The independent
`FINISH-CHECKPOINT.json` verifies1,258 evidence hashes and the complete bindings.
Build, fresh-compile, full type/assumption and six review logs are archived.
Preparation and review are not full normal acceptance.

## Next acceptance boundary

Keep the live407 tree frozen. Its guarded source-only integration requires
real actual-main401 and isolated407 success; the former is complete, while407
audit23810 is still running. The tested407 integration guards are in
`../elements-output-nonce-admission/`. Do not install intermediate402/404/406
trees, nor change the407 candidate to include these proofs.

After guarded407 installation, a combined successor can undergo full acceptance
while the separate actual-main407 audit runs. A combined413 audit must retain
and verify both completed410 and413 review chains. Installation of the
successor then requires both real full results, not these snapshots/reviews.
No full413 audit, installer or main installation has been launched.

This proposed registry has120 missing public declarations and104 entries with
the explicit `memcpy_model` condition. The every-jet goal, shared caller/domain,
evaluator/library/fidelity and configuration obligations remain unfinished.
These receipts bind the actual dirty/staged source, not clean-HEAD reproduction.
