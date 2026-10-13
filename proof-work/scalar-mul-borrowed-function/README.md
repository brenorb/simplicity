# Borrowed-rhs scalar multiplication: complete internal function

The actual `f_secp256k1_scalar_mul` call for `r=a`, with a writable owned
32-byte input/output and a non-owned readable rhs, now includes real function
entry, a fresh uninitialized 64-byte product allocation, the checked multiply
and reduction calls, and real local-buffer free. Four output loads after free
are observed; their exact value is the product modulo the canonical group order.
The rhs remains readable and represented. No writability or ownership is
required for it.

This is **not** a public `scalar_multiply_lambda` equivalence theorem, a
normal-namespace integration, or new coverage. Public lambda still needs its
literal specification, the actual readonly global's initial/preserved
representation, reader/writer/cursor framing and the original jet's cleanup.

## Evidence

Three modules, seven results and two definitions, scratch namespace BorrowFC.
All three freshly rebuilt (session 47979, exit 0); assumption driver replay
55935 exit 0; untruncated nine-record contracts 8169 bytes; independent whole
dependency kernel 23722 exit 0. One result is closed, four inherit the existing
four classical/extensionality dependencies, and the two execution theorems
inherit those plus CompCert's two semantics parameters. Kernel context matches
the inherited 15-name allowlist and all unsafe categories are empty.

`manifest.json` pins sources and the immutable accepted multiplication base.
`REVIEW.json` pins compiled sources/objects, drivers, output and kernel log.
Neither objects nor build products are copied into main.

## Reproduction

Use the installed Coq 8.17.1 path and 65520 KiB stack. In
`/tmp/jet-scalar-multiply-integration.yIS07H/Coq`:

```sh
bash build-jets.sh --coqc \
  -Q /tmp/jet-scalar-mul-borrowed.a0JQl2 BorrowC \
  -Q /tmp/jet-scalar-mul-borrowed-function.j7aAnw BorrowFC \
  /tmp/jet-scalar-mul-borrowed-function.j7aAnw/<module>.v
```

Rebuild the three manifest modules in order, then the two drivers.
The independent checker uses those same -Q mappings, `--coqchk -silent -o`,
and root `BorrowFC.jet_secp_scalar_mul_borrowed_observed`.
From the repo, run `python3 -B proof-work/scalar-mul-borrowed-function/review.py`
and `test-review.py`. Archives are not build registrations.

## Continue

First establish the four actual `secp256k1_const_lambda` limbs from the
generated original global and `Genv.init_mem`, with readonly permission only.
Reuse that relation through allocation and through the real caller's frame.
Port the pinned `scalar_lambda = scribe256 lambda` and
`(unit >>> scalar_lambda) &&& iden >>> scalar_multiply` literally; discharge
the C-versus-spec operand order with a formal value bridge. Compose the
complete borrowed helper with the existing original reader, serializer and
private-local cleanup. Do not turn initialization, helper execution, output
or free into a new public precondition.
