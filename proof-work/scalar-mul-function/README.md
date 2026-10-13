# Complete original in-place scalar multiplication function

This archive extends the checked body in `../scalar-mul-caller` through the
**actual original function boundary**. It proves
`Clight2.eval_funcall secp_ge … (Internal f_secp256k1_scalar_mul)` for arguments
`[a,a,b]`, including entry, the uninitialized local array allocation, both
unchanged helper calls, void return and actual local freeing.

It is an internal function result, **not** an equivalence theorem for public
`simplicity_scalar_multiply` or `simplicity_scalar_square`. No registry,
canonical specification, production C or accepted snapshot changes occur here;
this milestone adds **zero** covered jets. The build is the existing LP64
assertion-disabled RECKLESS configuration.

## Checked interfaces

- `scalar_mul_caller_allocates`: from two initialized owned 32-byte operand
  regions, the real 64-byte allocation establishes the existing fresh product
  representation. Its eight cells have no initial value premise. Allocation
  freshness supplies separation; the body layout is `[l,a,b]`.
- `eval_scalar_mul_caller_inplace`: its only premise is the input
  representation. It derives complete original function execution, output
  ownership surviving the actual free, product modulo the canonical group
  order, and framing outside both operand regions. Entry/body/free execution
  and post-memory facts are conclusions, not assumed premises.
- `eval_scalar_mul_caller_inplace_observed`: also derives four actual
  `Mem.load Mint64` results of the form `Some (Vlong w)` in the post-free
  memory. Their weighted value is the product modulo the canonical group
  order. Exact symbolic carrier kinds are proved before observing the words;
  this is not merely an equality after a lossy decoding operation.

The two operand regions must satisfy the existing separation/ownership
contract. The destination is the first operand, so `r=a` is supported. The
distinct alias case `a=b` used by public square is **not** covered. The frame
guarantee is outside both operands; it does not claim preservation of the
second operand inside that footprint.

## Verification evidence

All three modules and both audit drivers were explicitly rebuilt successfully
(session 31450, exit 0). The whole-dependency kernel check ran after that final
rebuild, with proof sources frozen (session 86193, exit 0). The source,
compiled-object and log hashes are pinned in `REVIEW.json`; the full type and
definition report has 19,489 bytes, 16 result types and seven definitions.

Ten results are closed under the global context. Four representation results
retain the inherited four classical/extensionality dependencies. The two
execution roots retain those plus CompCert's `external_functions_sem` and
`inline_assembly_sem`. No new axiom is introduced. The dependency-wide kernel
context contains the existing 15 axioms; type-in-type, unsafe (co)fixpoints and
assumed positivity are all absent. These inherited dependencies are not
described as an assumption-free proof.

The production/canonical source identity check passed for 240 files, and the
immutable dependency fingerprint remained unchanged. Full AST regeneration
and the integrated public acceptance gate were **not** run.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 proof-work/scalar-mul-function/review.py
PYTHONDONTWRITEBYTECODE=1 python3 proof-work/scalar-mul-function/test-review.py
```

The reviewer also checks the frozen body and earlier helper receipts. Twelve
negative fixtures reject corrupted evidence in memory, without changing any
proof or acceptance snapshot. It requires the recorded local scratch artifacts;
the durable `.source` files here alone are not a substitute for those logs.

## Rebuild

Use Coq 8.17.1 / OCaml 4.14.4, CompCert 3.14 and VST 2.14. The frozen
dependency base is `/tmp/jet-scalar-integration.XAMDsw/Coq`; previously checked
body/helper modules are in `/tmp/jet-scalar-mul.lkomWj` (`MulC`). This archive's
compiled sources and receipts are in `/tmp/jet-scalar-mul-boundary.TchFPw`
(`LifeC`). These are narrow, separate namespaces, not recursive mappings of
all temporary directories.

```sh
export PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH
ulimit -S -s 65520
cd /tmp/jet-scalar-integration.XAMDsw/Coq
perl -e 'alarm 150; exec @ARGV' bash build-jets.sh --coqc -R /tmp/jet-scalar-mul.lkomWj MulC -R /tmp/jet-scalar-mul-boundary.TchFPw LifeC /tmp/jet-scalar-mul-boundary.TchFPw/jet_secp_scalar_mul_caller_alloc.v
perl -e 'alarm 150; exec @ARGV' bash build-jets.sh --coqc -R /tmp/jet-scalar-mul.lkomWj MulC -R /tmp/jet-scalar-mul-boundary.TchFPw LifeC /tmp/jet-scalar-mul-boundary.TchFPw/jet_secp_scalar_mul_caller_function.v
perl -e 'alarm 150; exec @ARGV' bash build-jets.sh --coqc -R /tmp/jet-scalar-mul.lkomWj MulC -R /tmp/jet-scalar-mul-boundary.TchFPw LifeC /tmp/jet-scalar-mul-boundary.TchFPw/jet_secp_scalar_mul_caller_observed.v
perl -e 'alarm 150; exec @ARGV' bash build-jets.sh --coqc -R /tmp/jet-scalar-mul.lkomWj MulC -R /tmp/jet-scalar-mul-boundary.TchFPw LifeC /tmp/jet-scalar-mul-boundary.TchFPw/boundary_assumptions.v
perl -e 'alarm 150; exec @ARGV' bash build-jets.sh --coqc -R /tmp/jet-scalar-mul.lkomWj MulC -R /tmp/jet-scalar-mul-boundary.TchFPw LifeC /tmp/jet-scalar-mul-boundary.TchFPw/boundary_contracts.v
perl -e 'alarm 300; exec @ARGV' bash build-jets.sh --coqchk -silent -o -R /tmp/jet-scalar-mul.lkomWj MulC -R /tmp/jet-scalar-mul-boundary.TchFPw LifeC LifeC.jet_secp_scalar_mul_caller_observed
```

Rebuild in manifest order; capture fresh terminal status, reports and hashes
when regenerating evidence. Old `.vo` files or this receipt do not verify an
edited source. Preserve the immutable base and older evidence. See
`CONTINUATION.md` for the public closure and the separate square alias case.
Signed atomic local commits only; never push.
