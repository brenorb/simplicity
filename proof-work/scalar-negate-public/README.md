# Complete original scalar-negate public local contract

`NegC.jet_secp_scalar_negate_local.scalar_negate_local_spec` proves the
unchanged original `f_simplicity_scalar_negate` against its literal canonical
Simplicity term for **every Word256 input** under the inherited
`secp_jet_local_spec` frame contracts. It assumes no helper/public execution,
scalar representation, final output or successful freeing.

Actual entry allocates the 16-byte source frame and 32-byte scalar; the actual
by-value source copy is proved from frame storage. The reader establishes
exact canonical normalized limbs and caller ownership, which supply the
negation helper's precondition. Its actual in-place execution supplies exact
literal scalar-negate storage and the serializer's owned representation.
The source cursor and local permissions are preserved through negation.
The actual serializer writes precisely the canonical encoded result;
the public call returns true, actually frees both locals, and preserves
loads outside the allowed frame/output footprint.

Reuse: scalar-zero's actual allocation/copy/free infrastructure; the checked
scalar reader, serializer and scalar-normalize writer call node; exact
negation/carry/mask/storage results in `../scalar-negate`; and literal
multiply/mod512 bridges in `../scalar-negate-canonical`. The only new
specification identity permits reuse of the serializer; the public theorem
still states the literal scalar-negate term, not a numerical surrogate.

Five modules / eleven results were freshly compiled and independently
checked by `coqchk`. All eleven types, three new definitions and the full
inherited `secp_jet_local_spec` definition were reviewed untruncated.
Five results are closed, one uses only inherited functional extensionality,
and five execution results have the same four inherited classical plus
CompCert external/inline-assembly dependencies. No new axioms or libc model
premises; all three unsafe kernel categories are empty. Imported context:
15 inherited axioms.

The exact public/literal gate passes, including recursive program and
literal-add checks. Four public-contract mutations and eight strict evidence
mutations are rejected in memory, without changing audit inputs.
The earlier eight literal-wiring fixtures also pass. These source checks
supplement Coq; they are not a formal Haskell compiler/fidelity theorem.

Scope remains **local frames**, LP64 and unchanged RECKLESS/assertion-disabled
translation. General evaluator frames and assertion-enabled builds are not
established. This is a complete checked public local theorem, but **not yet
registered coverage or isolated full acceptance**. Main registry and other
authors' changes remain untouched.

Exact source/output hashes, commands and terminal statuses: `manifest.json`.
Reproduce from the repository root:

```sh
python3 proof-work/scalar-negate-public/review.py --work /tmp/jet-scalar-negate.f4CRAT
python3 proof-work/scalar-negate-public/test-review.py /tmp/jet-scalar-negate.f4CRAT
python3 proof-work/scalar-negate-public/test-literal.py /Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity /tmp/jet-scalar-negate.f4CRAT /tmp/jet-scalar-reverify.8hswEF /tmp/jet-ge-negate-accept.5mtyZa/Coq
```

Next: a separate normal namespace-C candidate containing the exact dependency
closure for scalar-normalize and scalar-negate, reviewed normal snapshots and
full acceptance without shortcuts, then careful main-checkout integration.
See `CONTINUATION.md`; do not repeat the already completed public caller.
