# Elements fee-classification proof boundary

Status at `d057851f`: **unresolved equivalence obligation, not a demonstrated
wrong result or a proved specification/implementation mismatch**. No target
source, API contract or generation setting has been changed.

### Later formal comparison

`jet_elements_fee_literal` ports the original `outputIsFee` combinator tree,
including its primitive, optional hash equality, constant and explicit-value
branches. `jet_elements_fee_compare.elements_output_fee_implementation_comparison`
combines the separated whole-C contract with an exact comparison against that
program. For every index and logical environment, the results disagree iff
the selected output exists, both asset and amount are explicit, its script
is nonempty, and that script's digest equals the empty-script digest. A C
true result always implies a canonical true result. The pure comparison
lemmas are closed; the combined C statement retains the six inherited
execution assumptions and the original representation/separation premises.

`jet_elements_total_fee_literal.elements_total_fee_sem` reduces the entire
canonical `totalFee` program to its exact finite output fold, retaining the
hash-based classifier, asset comparison and 64-bit carry discard. It covers
every environment in the existing domain, including zero outputs and the
largest permitted count. `jet_forWhile_fold_context` reuses the sequential
loop invariant while preserving the asset key as context. This is the
specification side of the cached-table comparison, not a new C-equivalence
theorem. No table-meaning or empty-digest converse assumption is introduced.

These modules compile in the ordinary build and pass reviewed scoped
assumption/contract comparisons. The existing amount source gate checks the
canonical fee program trees and literal definitions; the normal contract gate
checks theorem statements. Bounded static review found no semantic discrepancy.
These results establish neither a reachable collision witness nor the missing
cached-table correspondence, and add no public coverage. They do not turn
this boundary into a demonstrated bug. Reproduce their ordinary `.vo` targets,
scoped audits, and the existing `elements-amount-literal/check-source.py` and
`test-source.py` checks; logs remain temporary rather than part of this report.

## Expected versus implemented predicate

The fixed canonical program `outputIsFee` in
`Haskell/Simplicity/Elements/Programs/Transaction.hs:130` combines explicit
asset/amount tests with equality of `OutputScriptHash` to `emptyHash`.
Its `emptyHash` is `bsHash mempty`. For a present output with explicit asset
and amount, its final bit therefore tests the empty-script digest.

The original `isFee` in `C/elements/elementsJets.c:164` instead tests the
stored `emptyScript` flag and those two explicit prefixes. The real
`copyOutput` in `C/elements/env.c:248` sets that flag from script length zero,
independently of the script hash it also computes. The indexed
`simplicity_output_is_fee` caller at `elementsJets.c:478` emits that bit.

Thus the missing implication for actual builder-produced environments is:

```text
SHA256(script) = SHA256(empty)  implies  script is empty
```

Only scripts in the supported environment domain matter (the Coq port bounds
their length below 2^32). Empty scripts satisfy the digest test by equality;
the converse above is not supplied by the SHA execution proof. General hash
collisions, or a pigeonhole argument, do not establish a nonempty preimage of
this particular digest. No such script has been exhibited here, and the
converse has not been proved. Cryptographic infeasibility is not a formal
equality proof or authorization to add an assumption.

## Reproducible evidence and verification limits

Inspect the three source locations above, then build and check the C-side
execution modules with the pinned dependencies from `Coq/JET_BUILD.md`:

```sh
JET_TARGETS=C/jet_elements_fee_flag_caller.vo bash Coq/build-jets.sh -j12
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_elements_fee_flag_caller
```

`jet_elements_fee_flag_exec.eval_processed_isFee` derives the whole original
helper call from its initial flag/prefix loads, with unchanged memory and
empty trace. `jet_elements_fee_flag_caller.elements_output_fee_flag_contract`
composes the original indexed caller with the represented raw-script-empty
flag, including absent outputs and general valid separated frames. Its result
is explicitly `processed_fee_result`, not the canonical program above.
The endpoints retain the six inherited assumptions and no extra libc premise.
These checks establish C execution; they do not prove the missing converse,
the Haskell-to-Coq fee-program correspondence, or the real environment
builder's entire lifecycle. No native counterexample or bug reproduction is
claimed. Both modules passed independent recursive kernel checks and focused
no-update audits on their respective commits `c82ca174` and `d057851f`.

A concrete wrong-result witness would require a nonempty supported script
with exactly the empty-script digest, an output using that script with
explicit asset and amount, and consistent real builder-produced fields.
The two predicates would then differ at that output. A hand-built environment
with an inconsistent flag and hash would not establish that witness through
the actual builder.

## Impact and next work

### Original lookup comparison (internal execution progress)

`jet_elements_fee_lookup_compare.exec_fee_lookup_compare` executes the
original midpoint pointer load, `memcmp` call and comparison assignment.
Its source equality checks that slice against `f_lookup_fee`. The unsigned
division and pointer stride are derived from the actual AST; asset bytes
come from the represented midpoint entry. The result has the existing
`memcmp_model` sign relation and unchanged memory, without assuming a
particular comparison result. No new external model is introduced, and no
linked-libc correctness is claimed.

```sh
JET_TARGETS=C/jet_elements_fee_lookup_compare.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_elements_fee_lookup_compare
```

This is not a complete search, wrapper or canonical fee equivalence proof.
The full search iteration, sorted-table lookup argument, wrapper
composition and fee-classification boundary above remain open. It adds no
public coverage; the ledger remains 514/533.

### Original search branches and one iteration (internal progress)

`jet_elements_fee_lookup_branches.exec_fee_lookup_work` composes the
comparison with every original branch: matching assets return the stored
64-bit fee, otherwise the actual length and pointer assignments select the
lower or upper interval. The sign tests are derived from `memcmp_sign`, not
assumed comparison answers. Both next lengths are proved nonnegative and
strictly smaller for every positive represented incoming length, including
one-entry tables; changed and unchanged temporaries are explicit. Memory is
unchanged. `exec_fee_lookup_zero` proves the original zero-length exit without
reading the table or key and without an external-library premise.

The whole-iteration result retains the existing explicit `memcmp_model`
premise; the branch/zero-exit proofs themselves need no extra libc model.
All adapters are checked against the original statement tree and the fee
field offset against the generated composite layout. These are internal
execution results, not a replacement fee specification. Sorted lookup
correctness, the public wrapper and the hash-classification boundary remain
unfinished; complete loop composition is addressed below. No jet is
registered and coverage remains 514/533.

```sh
JET_TARGETS=C/jet_elements_fee_lookup_branches.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_elements_fee_lookup_branches
```

### Complete original lookup call (internal C contract)

`jet_elements_fee_lookup_loop.eval_fee_lookup_table` executes the entire
original `f_lookup_fee`, including function entry, every search iteration,
return conversion and local cleanup. Its result is exactly
`fee_lookup_answer (length entries) key entries`, with memory unchanged and
empty trace, under the existing explicit `memcmp_model` premise. The
iteration bound is discharged by strict decrease of each selected table
half; no loop execution, return value or termination is assumed.

`jet_elements_fee_lookup_table` represents the pointer array, each actual
entry's comparison bytes and fee load. Its slice lemmas preserve those
loads and pointer bounds. Empty tables need no key/table storage, allowing
NULL table pointers without an artificial nonnull premise.
`eval_fee_lookup_empty` separately proves that full call without a
`memcmp_model` premise for arbitrary initial key/table values.

The functional answer describes the C search choices; it is an internal
proof adapter, **not** a replacement for the canonical Simplicity fee
program. Correspondence of the real fee table to transaction outputs,
public-wrapper composition and the hash-classification boundary above still
need proof; sorted lookup is addressed below. No jet is registered;
coverage remains 514/533. Production C, ASTs, API and canonical
specifications are unchanged.

```sh
JET_TARGETS=C/jet_elements_fee_lookup_loop.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_elements_fee_lookup_loop
```

### Original lookup implements sorted key lookup (internal C contract)

`jet_elements_fee_lookup_sorted.eval_fee_lookup_sorted` connects the full
original C call to ordinary key lookup, not merely to its binary-search
choices. The sortedness predicate is the existing C helper's unique,
strict bytewise key order, stated on indices. The key lengths needed to
turn equal byte comparisons into equal keys are derived from the actual
storage relation. The proof establishes that a discarded half has no
matching key; it does not assume search completeness.

`eval_fee_lookup_present` returns the exact stored 64-bit fee for any
present matching key; `eval_fee_lookup_absent` returns zero if no key
matches. Both retain empty trace, unchanged memory and the existing explicit
`memcmp_model` premise. These are helper-level implementation results.
Establishing the real caller's sorted/unique fee table and relating its
amounts to canonical fee sums, plus public-wrapper composition and the
hash-classification boundary above, remain open. No production source,
canonical specification or API contract changes; no public registration or
new coverage. The ledger remains 514/533.

```sh
JET_TARGETS=C/jet_elements_fee_lookup_sorted.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_elements_fee_lookup_sorted
```

### Original total_fee lookup/write/return suffix (internal progress)

`jet_elements_total_fee_suffix.exec_total_fee_after_read` composes the real
environment field loads, complete sorted lookup call, write64 call and
return statement. Starting after `readHash`, it writes the exact looked-up
64-bit value and derives the usual output cells, cursor update, preserved
prefix, outside-memory frame and permission/valid-block preservation from
the existing writer contract. Its AST equality covers the original full
wrapper's statement shape; field offsets and linkage are checked against
the original Elements program. No expected lookup result or execution is
assumed.

The loaded table pointer must be defined, but need not be nonnull. Its
pointer-width type is derived from the actual memory load. In particular,
the initialized NULL used for an empty table is retained; an uninitialized
pointer is not treated as a valid builder-produced environment. The existing
`memcmp_model` premise remains explicit. This is a suffix proof, not a
whole-wrapper or canonical fee-equivalence theorem. The reader-to-key adapter
and whole-wrapper composition are addressed below; the environment and
canonical-fee connections above remain open. No public registration or
coverage change; the ledger remains 514/533. Frozen targets are unchanged.

```sh
JET_TARGETS=C/jet_elements_total_fee_suffix.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_elements_total_fee_suffix
```

### Original hash reader establishes lookup storage (internal progress)

`jet_elements_total_fee_read.exec_total_fee_read` executes the wrapper's real
`readHash` call and derives the lookup key from its eight stored 32-bit words.
It establishes the advanced input cursor and preserves loads outside the two
fresh caller-local blocks. The preservation lemmas transport the existing fee
table through these writes; lookup storage is derived, not assumed anew after
the call. An empty table still permits its actual NULL pointer.

This reader contract uses no external-library premise. The subsequent lookup
retains its existing explicit `memcmp_model` premise. Whole-wrapper composition
is addressed below; the environment and canonical-fee connections described
above remain open. This is not a whole-jet equivalence or a new public registration;
accepted coverage remains 514/533. Frozen targets are unchanged.

```sh
JET_TARGETS=C/jet_elements_total_fee_read.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_elements_total_fee_read
```

### Complete original total_fee wrapper (stored-table contract)

`jet_elements_total_fee_jet.eval_total_fee_stored_table` proves the complete
original `f_simplicity_total_fee` call. Its premises concern only the initial
frames, input word, represented stored table and its strict unique-key order.
The proof derives function entry and the two fresh local allocations, the
actual by-value frame copy, `readHash`, environment loads, complete lookup,
`write64`, successful return conversion and freeing both locals. No execution,
expected result, fresh-block separation or post-read representation is assumed.

The output is the exact stored-table lookup value for any 256-bit key. The
result includes arbitrary valid output cursors (including word crossings),
preservation of the prefix, updated cursor and framing of all original blocks
outside the actual output ranges. Empty tables permit the initialized NULL
pointer. The only explicit library premise is the existing `memcmp_model`.

This closes the wrapper execution obligation, not the canonical equivalence.
The real builder must still establish the represented sorted/unique table and
its sums' relationship to the canonical fee program. The hash-classification
boundary above remains unresolved. No public registration or coverage change:
514/533. Production C, original specifications, ASTs and API are unchanged.

```sh
JET_TARGETS=C/jet_elements_total_fee_jet.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_elements_total_fee_jet
```

`simplicity_output_is_fee` remains unregistered. `total_fee` also depends on
fee classification and the environment/table-to-canonical-fee bridge. In the
hypothetical witness case their classification or accumulated fee could
differ from the canonical programs; no reachable consensus failure, exploit,
monetary loss or native misbehavior has been established. The demonstrated
consequence is a missing exact equivalence proof, not a runtime bug.

Do not redefine `emptyScript` as digest equality, assume preimage uniqueness,
exclude a legitimate script, substitute the C classifier for the canonical
program, or count these intermediate execution contracts as accepted jets.
Any target correction requires separate explicit approval. Continue unrelated
proofs while preserving this boundary.
