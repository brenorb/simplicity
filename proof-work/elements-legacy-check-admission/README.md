# Legacy Elements lock assertions: normal-registration candidate

Proposed successor: **406/533**, adding only the two original-C
`broken_do_not_use_check_lock_{distance,duration}` jets after the reviewed404
candidate. Main is **401/533**, not406. This candidate is not installed and has
not passed full normal acceptance.

Private candidate: `/private/tmp/jet-legacy-check-admission.7fdc0wok`.
Prepared input SHA-256:
`9793dcb9faf3a1a73df4ca52e7054f1fdfc087ef1eb6bbfa266b06cdda79ec6f`.

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

## Completed preparation; independent finish review running

The normal build and explicit fresh compilation passed (83361, exit0).
All **8,415 inherited contract records** retain bytes/order, and all **5,527
inherited dependency sets** are unchanged. All thirteen new records have
untruncated reports; none requires an elision supplement.
`PREPARATION-CHECKPOINT.json` binds the read-only review, source, assembly,
preparation receipt and shared engine hashes. Full new contract/assumption
reports and build/fresh-compile logs are archived here. Generation is not
acceptance.

This batch reuses `normal-delta-prepare.py` unchanged. The immutable v1 review
engine remains byte-identical for earlier pending audits. Its new version,
`normal-delta-review-v2.py`, retains the same substantive delta/evidence checks
but delegates recognition of historical main input maps to the batch's exact
checkpoint resolver. This is needed because this candidate was prepared at
main401 while404 was itself prepared at399. Unknown maps still raise an error;
there is no permission for arbitrary main drift or mutation of predecessor
configuration. The source/evidence tests include an unrecognized input-map
corruption.

The six-stage finish review was launched once as **31051**:

```sh
python3 -B proof-work/elements-legacy-check-admission/review.py finish /private/tmp/jet-legacy-check-admission.7fdc0wok
```

Poll that handle; do not repeat a live or completed finish. It must pass
coverage, coverage-negative tests, ordinary contract comparison, canonical
source correspondence, source corruptions and independent evidence corruptions
before a `REVIEW.json` can claim completion. Its terminal status is not yet
recorded here.

No full406 audit or installation has been launched. They must follow the real
predecessor acceptance/installation chain, not a prepared snapshot or launch
record. Main401 audit **92989** and isolated402 audit **26900** are live; keep
their semantic inputs frozen. Next install402 only after both pass, audit its
actual main, then audit/install404, followed by this406 candidate. Scoped signed
commits go only to the brenorb fork, preserving unrelated dirty registries and
the entire original index.
