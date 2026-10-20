# Elements lock-height/time: literal programs and actual-C contracts

The new `jet_elements_lock_literal.v.source` proves full separated contracts
for `simplicity_tx_lock_height` and `simplicity_tx_lock_time` in `elements_ge`.
It reuses the existing C helper/function-boundary proofs and changes only the
specification presentation via proved equality. The public targets are the
canonical Simplicity compositions of `txIsFinal`, the LockTime primitive,
`parseLock`, zero, and sum elimination—not their mathematical return values.

The parseLock threshold explicitly uses the literal Haskell `toWord32`
state traversal (`haskell_to_word 5 500000000`). The shared all-width converter
proves its equality with the existing Coq word. The two generic source-program
matching lemmas are **closed**: they introduce no axioms. The actual-C endpoint
proofs retain exactly their originals' six inherited assumptions, with no new
library premise. No C execution or output property is assumed in place of a
proof, and no admission or unchecked cast is used.

## Checked evidence

Ten C proof/dependency modules were explicitly freshly compiled, followed by
the new literal module. The first experimental compile exposed an explicit
algebra argument mismatch; it was fixed using the installed
`Primitive.CanonicalStructures.toCore` projection. `check.py` subsequently
freshly recompiled the complete recorded closure, including both endpoints.
Only that successful run supplies the final receipts.

All 76 helper/final result types and 41 definitions have untruncated reports,
without unresolved placeholders. Per-result assumptions match the recorded
sets; both bridges remain closed and both literal C endpoints match their
originals' assumptions. Recursive `coqchk -silent -o` on the actual-C and
literal roots passed with unchanged inherited kernel context and no unsafe
fixpoint/assumed-positivity categories. Regenerating the production Elements
translation unit produced an exact `jets_elements.v` match.

The source guard reuses the checked finality loop and LockTime primitive
guards. It checks both canonical lock compositions; parseLock's threshold,
subtraction and borrow projection; recursive full-adder/complement/zero ports;
bit, routing, scribe and association conventions; the literal Coq programs;
and both complete original/literal C contracts. Thirty-two in-memory source
corruptions are rejected. Twenty-two further evidence corruptions reject
changed namespaces, sources, commands, inventories, bridge dependencies,
kernel/AST evidence and weakened contracts. Invalid proofs are never compiled.

The initial environment representation and all frame/memory guarantees are
unchanged. The transaction pointer, finality byte at offset 752, and 64-bit
lock carrier at offset 728 are related to the formal transaction, including
its unsigned 32-bit lock value. The footprint, cursor, output, prefix,
separation and function-boundary obligations are retained. This result does
not by itself prove that actual environment builders establish that relation,
evaluator composition, or assertion-enabled/non-LP64 configurations; the
existing LP64/RECKLESS model scope is unchanged.

## Continuation: no normal registration yet

Coverage added by this batch is **zero**. Do not change main's audited proof
inputs until its live sequence audit and the isolated direct-getter audit
have terminal results. Registration/full acceptance are not claimed here.

After the direct-getter batch is accepted and installed, prepare a separate
normal candidate for `tx_is_final`, `tx_lock_height`, and `tx_lock_time`.
Copy the literal proof into `C/jet_elements_lock_literal.v`, recheck it under
the final namespace and freshly compile every unregistered dependency. The
finality and lock modules share their loop, field-read and writer helpers;
do not duplicate those proofs or register helper-only entries as jets.
Both source guards and their negative suites must become mandatory gates.
Review complete statements, definitions, assumption deltas and inherited
record preservation before running the full normal acceptance command without
update/skip flags. Prepare an exact source-only installation ledger only after
that candidate and its predecessor have passed. All remaining jets and the
shared conditional-library/caller obligations remain in the all-jet goal.
