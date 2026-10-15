# Two output proof-hash C-to-specification endpoints

`simplicity_output_surjection_proof` and `simplicity_output_range_proof` now have
complete checked actual-C contracts against literal index/digest conversion
and explicit proof-byte views. The new module reuses
`elements_indexed_literal_matches` and the checked four-limb hash conversion.
It adds six results and four definitions, including two closed shared lemmas:
the proof-view adapter for every confidential payload carrier, and the indexed
output-proof digest conversion for every proof-byte projection.

## Evidence

Private tree: `/private/tmp/jet-elements-output-proof.saa7t23p`.
Fingerprint:
`2f544e32cc9734f30eaef5bb73f0bc36576f2572360b722c60909a59b5acd9cb`.
All 1,585 inherited source/metadata/registry files match the completed immutable
outpoint/output tree byte-for-byte. Only
`C.jet_elements_output_proof_literal` is a new source; the original execution
module compiles unchanged.

All 20 unregistered modules in the actual dependency closure were freshly
compiled. Full reports cover 219 result types and 142 definitions, preserving
apostrophe identifiers, without ellipses/evars. Every inherited dependency set
matches the earlier checked receipts. New C endpoint assumptions equal the
originals' six inherited assumptions; the two shared lemmas are closed.
Recursive kernel checking of the original execution root and new module passed
with the unchanged library context. Exact Elements AST regeneration passed.

The source guard checks both canonical catalog/primitive bindings, proof-byte
carriers and `prf_` cases, Asset/Amount adapters, selected Coq clauses, literal
models, cached digest words, and all four original/final whole C contracts. It
reuses the checked indexed-result, outpoint/output, digest, and current-program
guards. It rejected 35 in-memory corruptions. Independent evidence review
rejected 23 source/scope/inventory/command/report/kernel/AST corruptions. Invalid
proof fixtures are never compiled.

`PREPARATION.json` binds complete inventories, source/object hashes, checked
ancestor receipts, exact commands and successful terminal statuses, logs,
unchanged main inputs and original index. `EVIDENCE-REVIEW.json` separately
binds the independent review and its negative tests. Reports and all eight
source/type/assumption/AST/kernel/review logs are archived here.

```sh
python3 -B proof-work/elements-output-proof/review.py
python3 -B proof-work/elements-output-proof/test-review.py
```

## Exact behavior and remaining admission

Invalid indexes return the absent-output tag. Every valid output returns a
digest, including SHA-256 of empty proof bytes for explicit values; an empty
proof is not an absent output. Confidential values select their proof bytes.
The C jets copy cached words at offsets 36 and 68 within 248-byte outputs,
using the array/count fields at 8/704. Their initial environment relation
requires those words to represent `Digest.byteStringHash` of the selected
proof view. Caller construction of that cache is not established here.

Original frame/cursor/prefix/footprint and memory-change contracts remain
unchanged, as does LP64/RECKLESS. No new axiom, unchecked cast, or external-
library premise is introduced. The guard reviews selected source
correspondence, not formal host-lens/compiler/cryptography equivalence.
Receipts bind the actual dirty/staged base, not clean-HEAD reproducibility.

Coverage added here is **zero**. Main remains 378/533, with actual-main audit
3224 and isolated 386 audit 87596 confirmed live in their later acceptance
gates during this checkpoint. Do not edit their inputs or restart by silence.

These two jets are being combined with the reviewed eleven-getter batch into
`../elements-thirteen-getters-admission/`, proposing 399/533 over 386, to avoid
separate full audits for eleven and two. The earlier eleven-getter candidate
is preserved, not accepted or installed. The delta for this pair additionally
registers the existing execution module (eight results/eight definitions) and
the new literal module (six results/four definitions). Mandatory source and
negative gates, reviewed normal type/definition/assumption deltas, exact
coverage negatives, full acceptance, guarded source-only installation, and
actual-main acceptance remain required. The full all-jet goal is unfinished.
