# Elements count-jet continuation

This goal phase leaves the existing staged/unstaged work and normal registry
unchanged. Its two new checked sources are archived under `source/` and installed
source-only as `Coq/C/jet_elements_count_{constructible,payload}.v`. Compilation
and checking happen in copied trees outside the repository; no objects are
installed into the main checkout.

`jet_elements_count_constructible` constructs the physical count relation
for every logical `Elements.env` and composes the existing original-C local
contracts with fresh-frame construction. The final two results contain real
`Clight2.eval_funcall elements_ge` calls returning one and encoded canonical
outputs, with no environment-representation, frame or libc premise supplied.
Their starting C memory is existential; they do not replace the unrestricted
local contracts with a fresh-only contract or prove the production environment
builder. A shared offset/64-bit-carrier constructor handles both counts.

`jet_elements_count_payload` strengthens the specification boundary: the two
original C functions satisfy unrestricted local contracts against the literal
`first_fail_program`, for **any** total Word256 payload mapping on indexed
inputs/outputs. Count observes only Left/Right lookup presence, not the returned
hash. This is a formal C execution/output/prefix/cursor/memory theorem, not
merely a list-length identity. It preserves the original count contracts and
does not assume the execution or output that it concludes.

Replay with the pinned Coq 8.17.1 / CompCert 3.14 environment:

The helper reuses only source-identical objects bound to the earlier checked
normal integration receipt, and recursively checks them again. Missing cache
objects cause fresh compilation. The standalone support module avoids requiring
an unpushed historical branch merely to load the runner. The new sources
and four selected count modules never reuse compiled objects. Main Coq/C/
Haskell input and staged-patch fingerprints are checked before completion.

The selected source guard reviews the Haskell catalog/library dispatch, literal
`firstFail`/`forWhile`, assertion root, 32-bit carrier, indexed-lookup presence,
primitive identity, original-C target and initial environment relation. It
rejects 49 source corruptions and deliberately accepts a payload-only mutation,
justified by the any-payload theorem. Sixteen separate evidence-corruption tests
reject invalid inventories, commands, flags, objects, logs and exit statuses.
Full predicate/spec definitions are printed without truncation. This does not
claim hash-payload fidelity or review of unrelated Elements primitives.

Coverage remains 364/533. The count local contracts existed as unregistered
candidates; the new results discharge their non-vacuity/environment premise and
their hash-payload dependence, and the selected canonical-source observation
review is complete. A separate registry/snapshot/full-acceptance batch remains
required before counting these two jets as admitted coverage. Do not equate a
source guard or the shared list-count lemma with a C execution proof, and do
not treat this scoped audit as whole-checkout acceptance. Existing unchecked
conversion proofs elsewhere in the secp tree were subsequently repaired in
[`secp-checked-conversions`](../secp-checked-conversions/README.md), removing
that source-policy obstacle to a broader normal-registry rebuild.

Domain: the Coq Elements environment requires counts below 2^32. This is the
representable C raw-transaction interface (`uint32_t numInputs/numOutputs`),
not a claim about arbitrarily large Haskell vectors. Haskell `primEnv` checks
the current index but does not itself enforce the count bound. Caller-domain
review must keep that distinction explicit. The complete Elements transaction
builder proof remains outside this phase.
