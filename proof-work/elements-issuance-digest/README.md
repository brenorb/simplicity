# Six optional issuance-digest C-to-specification endpoints

The indexed/current `reissuance_blinding`, `new_issuance_contract`, and
`reissuance_entropy` jets now have complete actual-C contracts against literal
index/digest conversion. One shared closed adapter instantiates the checked
optional-digest lemma; the current variants reuse the checked
`CurrentIndex >>> assert (primitive ...)` semantic bridge. No admission, new
axiom, unchecked cast, or new external-library premise is introduced.

## Checked evidence

All 25 unregistered dependency/root modules were freshly compiled. The full
reports contain 257 result types and 193 definitions, including all apostrophe
identifiers, without ellipses or unresolved evars. The new module contributes
13 results and six definitions: one closed adapter, six semantic bridges, and
six full C endpoint theorems. Endpoint assumption sets exactly match the six
inherited execution assumptions of the originals; the pure adapter is closed.
Recursive kernel checking of the indexed, current, and new-module roots passed
with the unchanged library context. Exact Elements AST regeneration passed.

The source guard checks the Haskell catalog, optional `Either` projections,
direct hash fields, identities, current programs/library bindings, corresponding
Coq clauses, tag and hash representation, literal definitions, and all twelve
original/final whole C contracts. It rejected 75 in-memory corruptions. The
independent evidence reviewer rejected 23 source/scope/inventory/command/report/
kernel/AST corruptions. Invalid proof fixtures are never compiled.

## Cases and remaining admission work

Invalid input index, valid input with no issuance, valid input of the wrong
issuance kind, and valid input of the selected kind remain distinct. Blinding
and entropy select reissuances; contract selects new issuances. The selected
digest is copied directly, never hashed again. The tag is at issuance-relative
offset 272; the union fields are at 0 and entropy at 72, within a 544-byte input
whose issuance begins at 256. Existing output-prefix, cursor, frame separation,
environment footprint, and memory-preservation contracts are retained, along
with the LP64/RECKLESS configuration. Caller construction of the environment
relation is not established here.

After both succeed, guard and install the reviewed 386 candidate source-only,
preserve the entire preexisting index, and run its separate actual-main audit.
Then combine these six endpoints with the two checked annex endpoints for a
reviewed next batch (proposed 394/533). The new module's thirteen results/six
definitions are additive to the annex delta. All execution dependencies are
already registered by 378. Add exact nested-sum/domain/codomain/function/global/
environment coverage negatives, mandatory source/negative gates, full reviewed
snapshot/dependency deltas, complete normal acceptance, and guarded source-only
installation. Do not count helper compilation as accepted coverage.

The separately compiled `../elements-outpoint-output/` experiment adds a generic
indexed-result conversion and previous-outpoint/output-script-hash endpoints;
its own canonical review and admission remain distinct. Include it in a later
batch only after those checks succeed. The all-jet objective and inherited
fidelity, caller/library, and configuration obligations remain unfinished.
