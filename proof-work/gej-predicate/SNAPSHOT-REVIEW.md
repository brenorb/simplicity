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

Review so far inspected the actual public remainder/setup/entry/call/final
types, literal/parametric bindings and the concrete point/source ownership,
statement and temporary definitions. They retain the intended canonical bit,
actual original calls, ownership/cursor framing and complete final contract.
This does not claim manual review of every node of the 65,000-line computed
reader tree or completion of an old-record/standard-snapshot diff. The closed
execution witnesses have exact archived source hashes and kernel-proved run
equalities; deep prints supplement their later standard-depth truncation.

Preliminary ordinary-depth contract printing **79041 passed, exit 0**.
Driver `predicate_contracts_standard.v` SHA-256
`de8a932dc103fd1d18be642faebd16100b9397d5e45b7f64d71c00c05f3c14fa`.
Output `contracts-standard.out`: 10,467 lines / 857,052 bytes, SHA-256
`67b1bed633f15a43b56f15fe7b4510aa0260fc0381e979b44f60d8786ee0e4bd`;
stderr empty. Printing All/Width 120 are unchanged; no depth override.
All 62 types and 21 definitions are present. 60 types/17 definitions match
the deep report exactly modulo whitespace. `eval_point_read_fe` and
`eval_point_three_readers` contain truncated numerals; `point_read_run`,
`point_read_tree`, `point_zero_run` and `point_zero_ret` contain truncated
numerals or generated states. All their retained fragments match the deep
report in order. This textual ellipsis diagnostic is not structural equality
of omitted terms: exact archived/materialized source hashes and independent
kernel evidence remain required. Deep supplements contain no ellipses.

Supplemental scoped source/lifecycle correspondence now passes and all 37
meaningful negative fixtures are rejected, terminal exit 0. The exact scope
and reproduction commands are recorded in `SOURCE-REVIEW.md`; this is not a
replacement for inherited field-zero fidelity, AST or acceptance checks.

Remaining: isolated full standard snapshot generation, exact unchanged-old-record reconciliation and
fresh full acceptance without update flags. Dependencies include the newer
field-add rebase support and separately reviewed infinity support. No public
coverage or checkout proof input is changed by these preliminary artifacts.
