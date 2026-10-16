# Shared application-jet contextual contract

Private tree: `/private/tmp/jet-null-data-context-contract.oxOG8kkO`.
The two new modules are archived under `source/`; inherited sources equal the
checked `../elements-null-data-environment/` tree byte for byte. Main418
semantic inputs and the original staged patch remain unchanged.

## Exact contract and jet theorem

`C.jet_application_context_contract.application_jet_bitmachine_spec` is shared
infrastructure for successful application jets. It is parameterized by the real
C function/global environment, logical environment type, Simplicity input/output
types, an input-independent memory/environment relation, and the specification.
It explicitly requires represented/separated Bit Machine frames, output write
permissions/capacity, canonical input cells and separation of the environment
footprint from the output. It concludes the exact specification result, actual
CompCert call returning true, and representation of the expected output state
with the active read frame and inactive frames preserved.

The environment relation's type has no input value, frame layout or execution
parameter. Input/output separation is a stated caller invariant, not hidden in
that relation. The contract writes through canonical `encode`; it imposes no
special zero initialization, padding, cell-block identity distinction or chosen
cursor alignment beyond the existing representation.

`elements_output_null_datum_bitmachine_spec` proves this exact contract for the
actual Elements null-data C function and `prim Elements.OutputNullDatum`, using
the independent environment relation. It reuses the checked complete entry,
copy, read/output/return/free and state-preservation chain. This is not a
specification-only result and takes no assumed C execution or desired output.

## Domain and admission boundary

This is **not** the broader `application_jet_local_spec_sep`, which alone does
not protect unread input from output writes. The new contract names its
evaluator-valid domain explicitly; the existing separated streaming-jet
infrastructure establishes the same caller-layout discipline. It does not
replace old contracts or claim unrestricted overlapping-buffer correctness.
The header/API overlap finding remains open in
`../null-data-overlap-probe/README.md`.

The relation still assumes physical opcode/parser/cache correspondence; the
real Elements environment-builder establishment proof is separate. Likewise,
representation maintenance by the real C evaluator is not proved by this jet
theorem. All22 datum constructors, missing indices, non-null-data scripts,
empty parsed lists and empty output arrays are retained by the proof chain.

Before normal admission, review canonical Haskell/Coq-port fidelity, especially
the full null-data parser/encoding and selected primitive clause, and teach the
contract gate to validate this **exact contextual contract** as a distinct
domain. Do not add an opaque alias, relabel it as an unrestricted local result,
or count a source snapshot as acceptance. The target remains the pinned
assertion-disabled Elements program.

No main C, header, primitive, registry or acceptance snapshot changed.
Registered coverage remains418/533, not419; the all-jet goal remains unfinished.
No clean-HEAD reproduction is claimed for the dirty main tree.

## Verification

Both new modules compiled with pinned Coq8.17.1 / CompCert3.14. Fresh checker
98943 exited0 after explicitly recompiling both, printing the endpoint's full
type and shared contract definition without elision, regenerating the Elements
AST and recursively kernel-checking both roots and their dependency chain.
Independent evidence review40421 exited0 with38 deliberate proof/evidence
corruptions rejected. The separate terminal postcheck revalidates receipt/log/
tool hashes, fresh source/object identities and unchanged main inputs before
commit.

The endpoint has the six inherited Coq/CompCert assumptions and no new axiom,
admission or unchecked operation. The isolated `whole_c_endpoints=1` is not
normal registration, added coverage or full acceptance.

```sh
python3 -B proof-work/elements-null-data-context-contract/review.py /private/tmp/jet-null-data-context-contract.oxOG8kkO
```

The only development correction was using the installed word representation's
explicit four-bit type `(Word 2)` instead of a nonexistent `Word4` alias. The
new theorem's completed proof is a direct application of the checked
environment/Bit Machine endpoint under the shared contract definition.
