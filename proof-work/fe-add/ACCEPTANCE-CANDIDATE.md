# Isolated literal field-add acceptance candidate

## Latest receipt and integration

Isolated full acceptance **54093 passed with terminal exit 0** on 2026-10-09,
input SHA-256 `c4e91d0d6bbfb9d88fd63c40a802b5e052ecb8df2d54e51ec9b8a49e074b607d`.
The 38 guarded proof/checker/metadata/snapshot files are now integrated
byte-for-byte into the checkout. Only the new source modules/checkers are
committed as signed local **62350724**; shared metadata remains mixed with
preserved earlier staged work. No push. Full actual-checkout acceptance
**96671** is live; frozen input fingerprint
`16594c779a885f405041d02315d3cbaec414f439dc78c3d219dde3a8b425f631`.
The older text below records assembly history, not current process status.

Root: `/tmp/jet-add-accept.qwqWy1`; Coq tree: `Coq/`; exact materialized
archive: `ports/`. This is not integrated or accepted coverage.

The candidate copies the frozen negation tree under
`/tmp/jet-negate-accept.ftWsqQ/Coq` without hardlinks or writable links to its
proof/build outputs. C and Haskell links point to the unchanged production
checkout. Negation's isolated full acceptance 57174 has since passed with
exit 0, and its reviewed sources are guarded-integrated into the checkout.
The separate actual-checkout acceptance 57052 remains live. This addition
candidate does not modify either tree's frozen proof inputs.

## Assembly and completed checks

- All 31 archive records were extracted using `manage.py` into `ports/`.
- All 26 proof modules under `Coq/C/` match their archived hashes exactly.
- The ten infrastructure files match `INTEGRATION-PREPARED.json` exactly.
  Both project inventories include the 26 modules; the public inventory adds
  63 results, and the definition inventory adds 20 definitions.
- Only `C.jet_secp_add_local.fe_add_literal_local_spec` is newly registered.
  The inherited negation candidate row remains provisional. Candidate metadata
  is therefore 351/533, while actual accepted coverage remains 349/533.
- All 893 other inherited audited inputs are byte-identical to the negation
  candidate, including its snapshots and kernel allowlist. No existing public
  statement or assumption record was edited during assembly.
- The actual coverage suite passes with exit 0 (20653), including the four new
  field-add metadata mutations. The proof scanner passes, and the wired scoped
  source gate passes and rejects all 52 specification/lifecycle mutations.
- The previous whole public-chain kernel receipt 91932 remains evidence for
  the archived proofs, not acceptance of this assembled candidate.

Pre-snapshot assembled input SHA-256:
`78fd5e0edc985154de2fbdc28ca9decbcb0f81ad661d9a546941fcd59ad55f9a`.
It includes unchanged inherited snapshots, which deliberately do not yet
contain the field-add extension. This is not an acceptance fingerprint.

## Live build and next boundary

Fresh whole candidate build **24847 passes with exit 0**, log
`/tmp/jet-add-accept.qwqWy1/build.log`, through `build-jets.sh -j2`, with Coq
8.17.1 and a 65520 KiB stack. The baseline copy refreshed source timestamps,
so this build also recompiles inherited modules. All 26 added modules and the
inherited project closure were built. This is a terminal build receipt, not
full acceptance.

Actual standard snapshot generation is complete in this isolated tree:
assumption session **71393**, `assumptions-update.log`, and contract session
**57349**, `contracts-update.log`, both pass with exit 0. Contract generation
the actual diff inserts 1592 lines and removes/replaces none, preserving every
old printed type/definition verbatim and in order. The exact added 63 types
and 20 definitions are now reviewed; all match the preliminary actual prints
apart from qualification/white space, with unchanged source hashes. See
`SNAPSHOT-REVIEW.md` for scope and the standard snapshot SHA-256. Assumption
generation **71393** preserves every one of the 3670 old records and adds
exactly the 63 previously reviewed records, with no new axiom names. There
are 3733 records, 1948 closed. Both exact diffs are now reviewed. Generation
used the standard scripts with `--update`, Coq 8.17.1 and the 65520 KiB stack.
Separate full acceptance **54093** is now live with no update flags, log
`/tmp/jet-add-accept.qwqWy1/accept.log`. The candidate inputs are frozen.
Poll that same live handle; do not restart on yield.
Do not replace the ordinary snapshot printer to hide old-record changes.
The deeper preliminary field-add print review remains separate evidence.
Guarded integration and actual-checkout acceptance are still required.
The independently accepted negation candidate is now guarded-integrated into
the actual checkout; its separate checkout acceptance is live as 57052. This
does not change the field-add candidate's frozen proof or generated snapshots.

No production inputs or accepted Coq inputs changed. No new axiom or unsafe
kernel mechanism is introduced. No commit or push is claimed.
