# Issuance token-amount getters: reviewed normal417 candidate

Proposed successor: **417/533**, adding issuance_token_amount and
current_issuance_token_amount over the reviewed415 source. This is not full
acceptance or main installation.

Private tree: `/private/tmp/jet-token-admission.ngw4e2fw`. Exact source identity
is recorded in `REVIEW.json` and independently checked in
`FINISH-CHECKPOINT.json`. Main was407 during this review and is now the guarded,
accepted415 source tree. Its semantic sources and the original staged patch
were preserved throughout candidate preparation/review. No compiler objects
were copied from a live audit.

## Complete proof scope

The six-module checked bundle is in `../elements-token-bundle/`, with original
proof sources archived in `../elements-token-amount/`,
`../elements-token-select/` and `../elements-token-amount-complete/`.
Registration audits **all36 results and31 definitions**, including the generic
local-allocation/framing lemma, not merely the two final aliases.

These are complete C indexed/current contracts: absent issuance, new issuance,
and reissuance's actual local explicit-zero initialization, helper calls,
allocation/free, arbitrary valid frames/cursors/output contents and permitted
memory changes. The final aliases each retain the six inherited Coq/CompCert
assumptions. Thirteen shared results are closed. Caller environment
construction, host-library equivalence and other global fidelity/configuration
obligations are not discharged by this registration.

## Preparation and independent review

Preparation67049 and six-stage review5743 terminated with exit0. The normal
build and explicit fresh compilation of all six modules passed. All8,475
inherited contract records retain bytes/order and all5,563 inherited dependency
sets remain unchanged. All67 new records have full deep reports; one compact
record (`token_issuance_tail`) is supplemented by its complete deep rendering.
The shared preparation and review engines are unchanged.

Coverage checks, the ordinary contract comparison,14 new statement-confined
coverage fixtures, canonical/source checks,49 source-corruption tests and37
independent normal-review corruptions passed. The checkpoint independently
verifies1,270 evidence hashes, tool/engine identities and terminal commands;
all build, fresh-compile, full type/assumption and six-stage logs are archived.

The original candidate `/private/tmp/jet-token-admission.71nyklfh` failed its
ordinary contract comparison (9428, exit1): the normal printer imported
`jet_local_alloc_effect`, whereas preparation kept that new generic module
qualified. Four printed names differed. The rule was corrected specifically
for that module; no proof or desired snapshot contract was weakened. The
failed tree is retained untouched, with its receipts and diff in
`failed-printer-attempt/`. The new candidate was assembled and prepared afresh,
and a negative fixture checks removal of the corrected Require-only rule.

## Full acceptance and integration still required

`accept.py` requires real isolated415 acceptance and its guarded exact-main415
installation before launching the isolated417 full audit. It validates all
six review commands, fresh objects/reports, tools/engines, source and index,
and refuses duplicate launches. A full417 result is not claimed here.

`prepare-integration.py` plans only19 source targets: eleven metadata/scripts,
two canonical guards and six new proof modules. It refuses inherited proof
overwrites, compiler objects and unrelated source changes. Planning requires
the actual installed415 predecessor. It completed as22737 with exit0 after
guarded415 integration; `INSTALLATION-PLAN.json` binds the exact19-source delta,
both complete source identities, reviewed proof chain, tools and preserved
staging. Installation417 must additionally wait for real successful
actual-main415 and isolated417 receipts, then receive a separate actual-main417
audit.

The once-only installer and actual-main driver are now implemented. Logged
test86039 completed with exit0: all27 premature/unsafe source installation or
audit-launch conditions were rejected, with no writes or acceptance subprocess.
`INTEGRATION-REVIEW.json` binds the exact tools, plan and terminal log. No
positive417 installation or full audit has been run.

The preferred next audit is now the combined418 candidate in
`../elements-txid-admission/`: these two token endpoints plus the independently
reviewed transaction-ID getter, over the same exact415 base. Intermediate417
remains a separately reviewed delta, not an invented accepted installation.

The proposed registry has116 missing declarations and104 explicit
`memcpy_model` conditions. The every-jet goal remains unfinished. Receipts bind
the actual dirty/staged base, not clean-HEAD reproducibility.
