# Elements check-lock jets: literal assertions and both C return cases

The new `jet_elements_check_lock_literal.v.source` proves actual-C contracts
for `simplicity_check_lock_height` and `simplicity_check_lock_time` against
the literal canonical Simplicity assertion programs. The program is
`assert (iden &&& (unit >>> txLockHeight/Time) >>> le word32)`, using the
previously checked literal lock program and its word-conversion threshold.
The public target is not an integer inequality substituted for Simplicity.

The contract is `application_jet_partial_spec`, covering **every** valid input.
The C return value is true for `Some` and false for `None`. Successful calls
retain output, prefix and cursor guarantees, and memory framing is retained
on both success and failure. No success premise is added to hide failed
assertions. The initial physical/logical environment relation is unchanged.

## Reusable proof structure

`jet_application_partial_transport.v.source` adds the generic
`application_jet_partial_spec_pointwise`. Equality of specification results
transports the entire partial C contract, not just successful output.
The new check-lock program-matching lemma is axiom-free. The transport lemma
inherits the **same six assumptions** as the previously checked full-contract
transport, because its type references the existing CompCert semantics. It
must not be described as axiom-free merely because its proof is elementary.
Both final C endpoints retain exactly their originals' assumption sets, with
no new library model or assumed execution/output fact.

## Verified evidence

Private tree: `/private/tmp/jet-elements-check-lock.aYcKrW`.
Its inherited Coq source tree is an unchanged copy of the checked final-name
timelock tree (`../elements-timelock-normal/README.md`). The two new sources
are in `Proof/`, mapped narrowly to `CheckLockReview`, outside normal Coq
registration. No live acceptance-tree compiler outputs were copied.

Ten inherited C modules and the two new proof modules were freshly compiled.
All 77 helper/final result types and 40 definitions have complete reports,
without elision or unresolved placeholders. Assumption reports cover these
77 results plus one existing transport reference. The checker explicitly
requires the program bridge to be closed, the new contract transport to match
that checked reference, and both endpoints to match their originals.

An early evidence check correctly rejected classifying the contract transport
as a closed pure lemma. Inspection showed only the six inherited dependencies,
also present in the prior contract transport. The checker was corrected to
compare that reference exactly; its axiom-free requirement remains on the
actual program-matching bridge. The final receipt is from a subsequent fresh
compile/check run, not the earlier rejected classification.

Recursive `coqchk -silent -o` on the actual-C root and both new modules passed,
with the same inherited kernel context and no unsafe fixpoints/assumed
positivity. Regeneration of the production Elements unit matched the exact
`jets_elements.v` artifact. The source guard reuses the finality, lock and
assertion/hash-source correspondences, and checks the new literal composition,
`le`/borrow projection, whole original/literal contracts, full partial-contract
definition, failure return value and generic transport statement.
Twenty-five in-memory source mutations are rejected, including reversed
assertion branches, changed failure returns, weakened memory framing, wrong
functions/environments/widths and vacuous premises. Invalid proof text is
never compiled. The evidence review has additional scope/source/transport/
context/command/kernel/AST rejection tests.

`PREPARATION.json` binds the source base, original index, successful compiler/
checker commands, exits, source/object hashes, reports and tools. Both new
sources are outside the inherited Coq fingerprint and separately pinned by
source/object hashes and exact source guards. All source archives and full
contract/assumption/kernel/AST logs are retained here. This records the actual
dirty/staged source base, not clean-HEAD reproducibility.

```sh
python3 -B proof-work/elements-check-lock/review.py
python3 -B proof-work/elements-check-lock/test-review.py
```

## Next steps and scope

No normal manifests, registries, coverage or snapshots are changed by this
batch: coverage added is **zero**. First check both new modules under final
`C` names, changing only the helper import namespace. Then prepare reviewed
normal admission with the shared timelock dependencies, mandatory source and
negative gates, full statement/definition/assumption review and the unchanged
whole normal acceptance command. Do not treat compilation, kernel checking or
this preparation alone as normal admission.

Main's 368/533 sequence audit has passed in its actual checkout. The isolated
three-getter candidate remains a distinct pending full audit; main must stay
unchanged for that run's terminal source validation. Its installer still
requires both terminal results. Preserve the existing staged work and do not
restart completed or still-live audits.

These proofs do not establish environment-builder/evaluator composition or
broaden the current LP64/RECKLESS build scope. Simplicity assertion semantics
here must not be confused with enabling C's assertion macros. All other jets,
configuration coverage and shared conditional-library/caller obligations
remain in the original all-jet goal.
