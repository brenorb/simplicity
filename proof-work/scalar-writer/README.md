# Original scalar reader-to-writer bridge and whole writer execution

This local checkpoint contains 22 compiled, independently kernel-checked
support results across five modules. It adds no registered public jet coverage
and is not full acceptance of `simplicity_scalar_normalize`.

The exact radix lemma recovers four machine limbs, not merely equality after
lossy decoding. It derives the serializer's representation and its 32-byte
Freeable input storage from the unchanged reader's final representation, for
every Word256 input, including values at or above the group order.

The writer run is the unchanged `jets_secp.f_write_scalar`, with the existing
verified `write8s` implementation contract and actual scalar getter from
`secp_pure`. `xfun_top_sound` derives function entry, the real local 32-byte
buffer allocation, both helper calls, return and freeing. No call, final
output or successful free is assumed. The checked event bytes are connected
to the literal `canonical_scalar_normalize` Simplicity term through existing
numeric representation lemmas and canonical encoding. The complete writer
contract retains the caller's owned scalar and frame guarantees.

These are caller-local support contracts: the intended public caller must
establish the represented scalar storage, separation from external frames,
and the current output-frame invariant/capacity. Compilation and kernel
checking do not discharge the public jet's separate source-copy, entry and
return/free obligations. The unchanged LP64 RECKLESS/assertion-disabled AST
configuration remains the scope; other configurations are not established.

All 22 printed types and eight non-tree definitions were reviewed untruncated.
Per-result dependencies: 17 closed, three with the four inherited classical
dependencies, two execution results additionally with CompCert's external and
inline-assembly semantics interfaces. No new axioms, libc model or public
execution premises were introduced. The computed tree is diagnostic storage;
exact run and shape equalities are formal kernel-checked results.

Fresh checks used Coq 8.17.1, CompCert 3.14 and VST 2.14. Exact sources, drivers,
output hashes and terminal statuses are recorded in `manifest.json`. From the
repository root:

```sh
python3 proof-work/scalar-writer/review.py --work /tmp/jet-scalar-writer.khT8eN
python3 proof-work/scalar-writer/test-review.py /tmp/jet-scalar-writer.khT8eN
```

The negative fixtures modify reads in memory only, never the audit inputs.
Next: compose both actual calls, establish the original public call nodes,
then reuse the source-copy/entry/return/free structure for the public canonical
scalar-normalize theorem. Registration requires a separately reviewed and
fully accepted isolated candidate; main coverage remains unchanged here.
