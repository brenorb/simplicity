# Forced hash-source rebuild continuation

The original incremental receipts are preserved, but their full restored-source
claim is qualified in `../original-target-boundary/`. This private candidate is
`/private/tmp/jet-hashes-source-clean.dz7OGP`. Initial process **58864 terminated
with exit 1** at the diagnosed inventory-name check after the Coq targets and
reports completed. Its exact driver, logs and terminal classification are in
`first-attempt/`. The two expected names were corrected without proof changes.
A new complete forced verification **7014 passed with exit 0**. The independent
source-closure snapshot binds all **315** loaded local modules to that successful
forced build, including the original Bitcoin source. The source-bound recursive
kernel check **86762 passed with exit 0**. `SOURCE-CHECKED.json`, `CHECKED.json`
and `source-kernel-driver.log` record success with the full local source/object
hash set preserved. Do not restart or relabel these once-only checks.

Resource inspection found an active, CPU-bound compiler in the existing
`jet_sha_finalize_bridge.v`, about 1 GiB RSS and under its existing per-tactic
timeout. Quiet output is not termination. No compiler or source was changed.

The historical first-attempt metadata typo was in its driver, not a Coq proof:
its expected functional-extensionality inventory spelled the two composite semantic
lemmas `elements_outputs_hash_program_spec_sem` and
`elements_input_utxos_hash_program_spec_sem`. The real declarations, in the
unchanged archived source and complete reports, are
`elements_outputs_hash_spec_sem` and `elements_input_utxos_hash_spec_sem`.
The first strict inventory check refused that run after compilation/reports.
Its receipt was not relabeled as successful.

That original driver and all failed-run logs are preserved in `first-attempt/`.
The corrected driver then reran the entire forced build, producing the new
successful `RUN.json`. Do not repeat the old inventory repair.

The snapshot, once-only launch and successful terminal receipt are recorded.
They bind every local source/object hash before and after recursive checking.
The older incremental receipts remain qualified, not overwritten: the success
is this separate forced-source run only.

The literal companion's source is copied unchanged from the checked
`../elements-blinding-entropy/canonical/BlindingEntropy.v.source`; only its
logical module path is now `C.jet_elements_blinding_entropy_literal`. It is the
canonical endpoint, not a second jet to count alongside its intermediate
scribe-prefix helper. Caller cache relations remain explicit. No normal
registration/full acceptance or coverage increment is authorized by a launch
or partial build; the original Bitcoin identity gate remains unresolved.
