# Complete original scalar_normalize public local contract

`WriterC.jet_secp_scalar_normalize_local.scalar_normalize_local_spec` proves
the unchanged original `f_simplicity_scalar_normalize` against the literal
canonical Simplicity term, for **every Word256 input** under the inherited
`secp_jet_local_spec` frame contracts. The theorem assumes no helper/public
execution, scalar representation, final output or successful freeing.

Actual function entry allocates the 16-byte local source frame and 32-byte
scalar. The actual by-value source copy is derived from frame storage, then
both unchanged reader and writer calls execute with their local buffer
lifecycles. The reader supplies exact canonical limbs and ownership; these
construct the writer's representation. The output is exact canonical encoded
bits, the return is true, the caller's locals are actually freed, and loads
outside the frame/output footprint are preserved.

Reuse: existing scalar-zero local allocation/copy/free contracts, verified
scalar reader lifecycle and representation, and the whole original serializer
checkpoint in `../scalar-writer`. The old preparation theorem's one-bit
capacity is strengthened to 256 from the public output capacity; its other
facts are reused unchanged. The original normalize function has no temporary
locals: its entry uses its own exact temp environment, not scalar-zero's
different temporary list.

Four modules / eleven results were freshly compiled and independently checked
by `coqchk`. All eleven types and three definitions were reviewed untruncated.
Six results are closed; five execution results have exactly four inherited
classical dependencies plus CompCert external/inline-assembly semantics.
There are no new axioms, no libc model premise and no unchecked proof tactics.
Imported kernel context: 15 inherited axioms; all three unsafe categories are
empty. The literal public theorem gate passes, as do four public-contract
and eleven canonical/recursive in-memory negative fixtures.

This remains the inherited **local frame domain**, LP64 and unchanged
RECKLESS/assertion-disabled translation. It does not establish the general
evaluator domain or assertion-enabled builds. It is a complete checked public
local theorem, but **not registered coverage or isolated full acceptance**.
Main registries and other authors' changes were left untouched.

Exact materialized sources, drivers, output hashes and terminal statuses are
in `manifest.json`. Verification from the repository root:

```sh
python3 proof-work/scalar-normalize/review.py --work /tmp/jet-scalar-writer.khT8eN
python3 proof-work/scalar-normalize/test-review.py /tmp/jet-scalar-writer.khT8eN
python3 proof-work/scalar-normalize/test-literal.py /Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity /tmp/jet-scalar-writer.khT8eN /tmp/jet-scalar-reverify.8hswEF /tmp/jet-ge-negate-accept.5mtyZa/Coq
```

Next: after the frozen scalar-zero candidate finishes full acceptance,
assemble a separate namespace-C candidate containing this dependency closure
and the serializer checkpoint. Extend the literal/public contract gate to
scalar-normalize, review normal type/definition/assumption snapshots, and run
full `check-jets.sh --accept` without update/no-build shortcuts. Do not count
the new jet or change the currently running candidate until then.
