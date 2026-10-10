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

Actual per-result assumption generation **97828 passed, terminal exit 0**.
Driver `/tmp/jet-gej-predicate.W2FtCz/predicate_assumptions_review.v` SHA-256
`11ec6c61393533c042262558e256c3f36f40856d037042c675d3d2ede9522fd7`.
Output `assumptions-review.out`: 446 lines / 20,732 bytes, SHA-256
`9d17523874623cae0a39d1f4e4ff101ea189fd99b5b87ab7c4782d5aa2388c10`;
stderr empty. Actual reports cover all 62 unique inventoried results, 34
closed, and only six inherited axiom names. The final public theorem retains
the six inherited execution assumptions; no external-library model/new axiom
appears. The rows in `assumptions-provisional.expected.source` are derived
from actual output, not guessed theorem categories. The read-only parser
rejects missing/duplicate/unfinished sections and unexpected axioms; two
positive and seven negative report fixtures were checked.

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

The receipt `PRELIMINARY-REVIEW.json` contains actual per-result axiom sets
and print-comparison evidence. Reproduce the read-only preliminary review:

```sh
python3 proof-work/gej-predicate/review-preliminary.py \
  --work /tmp/jet-gej-predicate.W2FtCz --assumptions
```

Supplemental scoped source/lifecycle correspondence now passes and all 37
meaningful negative fixtures are rejected, terminal exit 0. The exact scope
and reproduction commands are recorded in `SOURCE-REVIEW.md`; this is not a
replacement for inherited field-zero fidelity, AST or acceptance checks.

Remaining: isolated full standard snapshot generation, exact unchanged-old-record reconciliation and
fresh full acceptance without update flags. Dependencies include the newer
field-add rebase support and separately reviewed infinity support. No public
coverage or checkout proof input is changed by these preliminary artifacts.
