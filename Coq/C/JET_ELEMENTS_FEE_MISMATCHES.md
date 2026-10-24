# Elements fee-classification proof boundary

Status at `d057851f`: **unresolved equivalence obligation, not a demonstrated
wrong result or a proved specification/implementation mismatch**. No target
source, API contract or generation setting has been changed.

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
execution results, not a replacement fee specification. Complete loop
composition over a represented table, sorted lookup correctness, the public
wrapper and the hash-classification boundary remain unfinished. No jet is
registered and coverage remains 514/533.

```sh
JET_TARGETS=C/jet_elements_fee_lookup_branches.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_elements_fee_lookup_branches
```

`simplicity_output_is_fee` remains unregistered. `total_fee` also depends on
fee classification and has further execution/lookup obligations. In the
hypothetical witness case their classification or accumulated fee could
differ from the canonical programs; no reachable consensus failure, exploit,
monetary loss or native misbehavior has been established. The demonstrated
consequence is a missing exact equivalence proof, not a runtime bug.

Do not redefine `emptyScript` as digest equality, assume preimage uniqueness,
exclude a legitimate script, substitute the C classifier for the canonical
program, or count these intermediate execution contracts as accepted jets.
Any target correction requires separate explicit approval. Continue unrelated
proofs while preserving this boundary.
