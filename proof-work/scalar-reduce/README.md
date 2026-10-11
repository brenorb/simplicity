# Scalar reduction value bridge

This is an internal continuation of `../scalar-next`, preserving its
`OriginalC` namespace and all 23 reviewed helper sources unchanged. It adds
one freshly compiled module with 20 completed results and 17 definitions.
No public jet coverage or full acceptance is claimed.

The final checked declaration is `eval_scalar_reduce_numeric`. From the
existing writable four-limb representation and the internally supplied
overflow flag, it proves the actual original Clight scalar_reduce call,
return flag, four current-memory loads, output value modulo the group order,
post-call representation and outside-footprint framing. The reader must
derive the flag from the actual overflow call; this is not a permissible
additional precondition on a public scalar jet.

The arithmetic decomposition is reusable: three arbitrary uint64 additions
and their two carry bits give exact quotient/remainder without restricting
overflow; the reduction's exact executor output is matched to those steps.
A weighted carry telescope accounts for the final 256-bit wrap. The bounded
canonical input and its derived comparison flag then identify that wrap with
reduction modulo the group order. Closed constants are normalized separately;
no symbolic-memory `vm_compute`, admissions, or new assumed declarations.

Verification on Coq 8.17.1 / CompCert 3.14 / VST 2.14:

- Final module compilation session 7519 exited 0.
- Independent kernel session 56508 exited 0, with 15 imported context axioms
  and all three unsafe categories empty.
- Per-result assumption session 51416 exited 0: 18 closed results; the memory
  load adapter uses four inherited classical/extensionality assumptions, and
  the actual-call theorem uses the same six inherited execution assumptions
  as the existing scalar helpers.
- Type/definition session 60930 exited 0: all 20 actual types and 17 definitions
  reviewed in the untruncated deep print, with empty diagnostics. Those prints
  document the internal flag/region boundary, not public equivalence.
- Both previous 86-result scalar-next dependency/contract reviews still pass.

The source and review drivers use `.source` to stay outside accepted load
paths. Their exact materialized files and logs are in
`/tmp/jet-scalar-reverify.8hswEF`; run `review.py --work` with that directory
to recheck the pinned evidence. To rebuild, use the unchanged normal candidate
Coq directory `/tmp/jet-ge-negate-accept.5mtyZa/Coq`:

```sh
export PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH
ulimit -S -s 65520
bash build-jets.sh --coqc -R /tmp/jet-scalar-reverify.8hswEF OriginalC \
  /tmp/jet-scalar-reverify.8hswEF/jet_secp_scalar_reduce_numeric.v
bash build-jets.sh --coqchk -silent -o \
  -R /tmp/jet-scalar-reverify.8hswEF OriginalC \
  OriginalC.jet_secp_scalar_reduce_numeric
```

Next: prove scalar_set_b32's byte assembly and its composition with the actual
overflow/reduction expressions. Derive its output value from the real 32-byte
reader buffer, without assuming correct output. Then prove read_scalar's
allocation/read8s/NULL-set/free, the public scalar_is_zero lifecycle and the
literal canonical specification/source gates. SHA and memcpy remain reserved
for the coordinated separate session.
