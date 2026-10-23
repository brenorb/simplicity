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
