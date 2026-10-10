# Predicate snapshot preparation (not accepted snapshots)

The final public whole-closure kernel **88320 passed with terminal exit 0**.
Its 15 context axioms match `Coq/C/jet_coqchk_axioms.expected` exactly and
type-in-type, unsafe fixpoints and unchecked positivity are all absent.
All 62 results now have independent public whole-closure kernel evidence.

`public-results.txt.source` contains every one of the 62 Lemma/Theorem
declarations in the 22 exact archived modules. `contract-definitions.txt.source`
contains all 21 top-level Definition declarations, including the literal
program, temporary environments, statement trees, storage predicates and
computed reader/zero-test witnesses. Inventories were checked against the
actual declarations, not inferred from a manually maintained count.

Preliminary deep contract printing **5474 passed, exit 0**. Driver:
`/tmp/jet-gej-predicate.W2FtCz/predicate_contracts_review.v`, SHA-256
`dcd1d8ae9b6dce69b14eda8bf4df0c8c5c9f43e0be21462444ef36b9dec5ae56`.
Output `contracts-review.out` in that directory is 68,924 lines / 6,505,926
bytes, SHA-256
`cd1068b27cd679284995fb4f7c84a570e9b4a75217d8c3f355ed1fd94a041b32`;
stderr is empty and no `(...)` printing truncation occurs. This used
Printing All, Width 120 and Depth 10000 and printed every inventoried type
and transparent definition. It did not update any standard expected snapshot.

Review so far inspected the actual public remainder/setup/entry/call/final
types, literal/parametric bindings and the concrete point/source ownership,
statement and temporary definitions. They retain the intended canonical bit,
actual original calls, ownership/cursor framing and complete final contract.
This does not claim manual review of every node of the 65,000-line computed
reader tree or completion of an old-record/standard-snapshot diff. The closed
execution witnesses have exact archived source hashes and kernel-proved run
equalities; deep prints supplement their later standard-depth truncation.

Per-result assumption generation is prepared but **not started**:
`/tmp/jet-gej-predicate.W2FtCz/predicate_assumptions_review.v` emits a marker
and actual Print Assumptions for every result. Run with the same Coq 8.17.1
toolchain / narrow C overlays once the current checkout build is terminal,
avoiding a repeat of heavy assumption printing concurrent with timed tactics.
Do not generate expected assumption rows from guessed theorem categories.

Supplemental scoped source/lifecycle correspondence now passes and all 37
meaningful negative fixtures are rejected, terminal exit 0. The exact scope
and reproduction commands are recorded in `SOURCE-REVIEW.md`; this is not a
replacement for inherited field-zero fidelity, AST or acceptance checks.

Remaining: complete preliminary assumption and contract review, isolated
standard snapshot generation, exact unchanged-old-record reconciliation and
fresh full acceptance without update flags. Dependencies include the newer
field-add rebase support and separately reviewed infinity support. No public
coverage or checkout proof input is changed by these preliminary artifacts.
