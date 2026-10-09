# Field-add preliminary new-record snapshot review

Isolated actual printing completed with exit 0 (84352), using the existing
compiled candidate and its narrow scratch load path. Log:
`/tmp/jet-fe-add-next.3vEywc/snapshot-review.log` (2120 lines).
This is not candidate-wide snapshot generation, old-record diff approval or
full acceptance. Accepted and negation-candidate snapshots were not edited.

The checked output contains exactly the manifest's 63 results and 20 transparent
definitions. Actual assumption sets are:

- 31 closed;
- 2 functional extensionality alone;
- 12 inherited logical assumptions (the two ClassicalDedekindReals decisions,
  classical excluded middle and functional extensionality);
- 18 the same logical assumptions plus CompCert external-functions and
  inline-assembly semantics.

The final public theorem belongs to the last group. No new axiom name or libc
model occurs. The public kernel context independently matches all 15 inherited
library axiom names, with all three unsafe categories empty (91932, exit 0).

The definition roles reviewed are five actual helper arguments/run/tree/state
definitions, five limb/value/storage maps, three literal one/expand/add programs,
two normalized reader environments, four public environment/statement mappings
and the actual public temporary environment. The symbolic state contains the
five original machine additions and retains both fields' Freeable metadata.
Numeric/normalized internal premises are discharged in actual readers and the
four-call/lifecycle composition. The final statement has the original full
Word256-pair contract and no intermediate execution/output/freeing premise.

Inspection found the default Coq printer abbreviates deeply nested terms with
`(...)`, including unary fuel constants and parts of the symbolic tree. The
first run is therefore insufficient for a fully explicit body print. A separate
review run sets `Printing Depth 10000` and **passes with exit 0 (55290)**,
retaining all original source/proof bytes. Its 2211-line log is
`snapshot-review-depth.log`: no `(...)` remains, both inventories match exactly,
and all 63 assumption sets are identical to the first run. The newly exposed
symbolic helper state retains all five additions, the unchanged second field
and both Freeable regions. The literal ports retain exact carry branches and
Word256/Word512 types; the three-local environment and temporary map match
the original body/entry. The per-result assumption records are preserved in
`assumptions-provisional.expected.source`. They are preliminary actual evidence,
not replacements for candidate-wide standard snapshots. The ordinary accepted
snapshot printer/configuration is unchanged; source correspondence and actual
fingerprinted inputs remain separate evidence.

## Actual candidate-wide contract snapshot review

The isolated candidate `/tmp/jet-add-accept.qwqWy1/Coq` has now completed
its whole build (24847, exit 0) and standard contract generation (57349,
exit 0). The actual `C/jet_contracts.expected` SHA-256 is
`88ecdae157d4e0cb48e906a2cb1c856483947744addb816309e05c4a1ee881dd`.
Comparison with the accepted negation candidate finds exactly two insertion
blocks: 1366 theorem-type lines and 226 definition lines, 1592 total. There
are no deletions, replacements or reordered existing records.

All 63 added types and 20 definitions were compared with the preliminary
actual print. They match after removing only module qualification and white
space, which vary with the full project's import context. This supplementary
text comparison is not a name-resolution proof; the actual printed records,
their defining sources and the fully qualified deep-print review were also
inspected. All 26 candidate proof source hashes match the reviewed archive.
The standard printer retains its existing depth abbreviations; its settings
were not changed. The separate depth-10000 print supplies the previously
reviewed expansion of those same unchanged source definitions.

The new public type remains the exact `secp_jet_local_spec` for the original
`f_simplicity_fe_add`, Word256-pair input and Word256 output, using
`literal_fe_add CoreFunSem`. The expanded lifecycle theorem assumes only
initial frame/input storage, alignment, capacity and representable cursors.
It concludes the actual public call returning true, literal encoded output,
the complete `finv` and outside-memory framing. Three local allocations,
source copying, both readers, arithmetic, writer and freeing are derived;
intermediate call/store/free premises occur only in support adapters and are
discharged by the public chain. No numeric substitute specification or new
public execution/output/cleanup premise appears.

## Actual candidate-wide assumption snapshot review

Assumption generation 71393 now passes with exit 0. The standard snapshot's
SHA-256 is
`41c7af44a93e3926fda725ac8eb978ec5de6aed7720309a051be477ad47d6b0f`.
Every one of the 3670 inherited records retains exactly its previous axiom
set. The only extension is the expected 63 results, byte-for-byte equal as
name/assumption records to the preliminary reviewed inventory: 31 closed,
two functional-extensionality-only, 12 inherited logical and 18 inherited
logical/execution-semantics results. There are 3733 total records, 1948 closed.
No new axiom or library-model premise is added; the final public contract
retains only the six inherited execution assumptions.

Both actual standard snapshot diffs are now reviewed. Separate frozen full
acceptance, without update flags, is live as 54093, log
`/tmp/jet-add-accept.qwqWy1/accept.log`. Generation and this review are not
acceptance. Preserve those inputs and poll that same handle until terminal;
guarded integration and actual-checkout acceptance remain subsequent steps.
