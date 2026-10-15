# Elements count-jet continuation

This goal phase leaves the existing staged/unstaged work and normal registry
unchanged. Its new checked source is archived under `source/`; extraction and
compilation happen only in a new copied tree outside the repository.

`jet_elements_count_constructible` constructs the physical count relation
for every logical `Elements.env` and composes the existing original-C local
contracts with fresh-frame construction. The final two results contain real
`Clight2.eval_funcall elements_ge` calls returning one and encoded canonical
outputs, with no environment-representation, frame or libc premise supplied.
Their starting C memory is existential; they do not replace the unrestricted
local contracts with a fresh-only contract or prove the production environment
builder. A shared offset/64-bit-carrier constructor handles both counts.

The new source and four count specification/bridge/local/executable modules
were freshly compiled in a 206-module C/support closure. Full exported types
and assumptions passed, the Elements AST regenerated exactly, and recursive
kernel checking passed. Assumptions stay within the six inherited assumptions;
no admission, extra axiom, disabled check, unsafe fixpoint or assumed positivity
was introduced. Receipts in `ASSEMBLY.json` and `REVIEW.json` record the exact
objects, source hashes, commands and actual exit statuses.

Replay with the pinned Coq 8.17.1 / CompCert 3.14 environment:

```
python3 -B proof-work/elements-count/run.py prepare
ulimit -s 65520
python3 -B proof-work/elements-count/run.py check /absolute/candidate
```

The helper reuses only source-identical objects bound to the earlier checked
normal integration receipt, and recursively checks them again. The new source
and four selected count modules never reuse compiled objects. Main Coq/C/
Haskell input and staged-patch fingerprints are checked before completion.

Coverage remains 364/533. The count local contracts existed as unregistered
candidates; these new results discharge their non-vacuity/environment premise,
not the canonical-source/admission review by themselves. The next step is the
literal Haskell `NumInputs`/`NumOutputs` dispatch, `firstFail`/`forWhile` and
selected indexed-primitive observation review with negative fixtures, then a
separate reviewed registration/acceptance batch. Do not equate a source guard
or the shared list-count lemma with a C execution proof.

Domain: the Coq Elements environment requires counts below 2^32. This is the
representable C raw-transaction interface (`uint32_t numInputs/numOutputs`),
not a claim about arbitrarily large Haskell vectors. Haskell `primEnv` checks
the current index but does not itself enforce the count bound. Caller-domain
review must keep that distinction explicit. The complete Elements transaction
builder proof remains outside this phase.
