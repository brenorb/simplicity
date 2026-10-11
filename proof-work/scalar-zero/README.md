# Complete scalar-zero implementation-to-literal local contract

`scalar_zero_local_spec` proves the original public
`f_simplicity_scalar_is_zero` against `canonical_scalar_is_zero`, the literal
Simplicity program port. Its input domain is **all Word256 values**, including
the raw secp256k1 group order; it is not restricted to normalized scalars.
The port checks the canonical program's disjunction of raw zero and equality
to the group order. Numeric reduction facts are internal bridges, not a
replacement public specification.

The proof derives original function entry, 16-byte source-frame and 32-byte
scalar allocation, actual by-value source copy, the complete original scalar
reader (including its 32-byte buffer allocation/release), original reduction
and zero test, writeBit, true return, and actual release of both public locals.
It proves encoded output, cursor updates and the inherited local memory frame.
There is no memcpy-model premise and no assumed public call/output/free fact.
Internal call adapters take helper executions; the complete caller discharges
them from the checked implementations.

Five modules contain 18 results and three definitions. Fresh compilation,
untruncated type/definition inspection, exact assumptions and independent
whole-chain kernel checking all succeeded. Kernel session 14762 exited 0.
Nine results are closed; two use four inherited classical/extensionality
assumptions; seven also depend on CompCert's two execution-semantic parameters.
The imported kernel context has 15 inherited axioms, with no type-in-type,
unsafe fixpoints or assumed positivity. The reviewer checks exact per-result
dependencies, source/driver/output hashes and successful terminal receipts.

This is **not yet full acceptance or checkout registration**. The public
theorem inherits `secp_jet_local_spec`'s LP64, assertion-disabled RECKLESS
configuration and local frame premises. It does not establish arbitrary
evaluator frame constructibility, assertion-enabled execution, whole evaluator
integration, or a new C/specification configuration. Registered main-checkout
coverage remains 351/533; this archive adds zero. The accepted affine isolated
candidate has 355/533 and is a separate baseline, not checkout integration.

```sh
python3 proof-work/scalar-zero/review.py --work /tmp/jet-scalar-reverify.8hswEF
python3 proof-work/scalar-zero/test-review.py /tmp/jet-scalar-reverify.8hswEF
python3 proof-work/scalar-zero/check-literal.py --repo "$PWD" --source /tmp/jet-scalar-reverify.8hswEF --coq /tmp/jet-ge-negate-accept.5mtyZa/Coq
python3 proof-work/scalar-zero/test-literal.py "$PWD" /tmp/jet-scalar-reverify.8hswEF /tmp/jet-ge-negate-accept.5mtyZa/Coq
python3 proof-work/scalar-reader-zero/test-literal.py "$PWD" /tmp/jet-scalar-reverify.8hswEF /tmp/jet-ge-negate-accept.5mtyZa/Coq
```

Reproduce with pinned Coq 8.17.1/CompCert 3.14/VST 2.14, stack 65520 KiB,
cwd `/tmp/jet-ge-negate-accept.5mtyZa/Coq`, using its `build-jets.sh` and
the narrow `-R /tmp/jet-scalar-reverify.8hswEF OriginalC` load path.
Compile prerequisites from the manifest in dependency order before the five
modules. The manifest records the independent kernel command and exact hashes.
`.v.source` archives are intentionally outside accepted project load paths.

Next: assemble a fresh isolated candidate over the immutable accepted affine
baseline, transport these modules to namespace C with fresh compilation,
review all added types/definitions/dependencies and literal-source gates, then
run normal full acceptance before registry integration. Preserve the checkout's
unrelated staged/dirty SHA and coverage work. Claude reserves shared memcpy
linkage, SHA startup and general core frame constructibility; our caller-specific
scalar lifecycle does not overlap those reservations. No remote pushes.
