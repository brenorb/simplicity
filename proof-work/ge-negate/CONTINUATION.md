# Affine negation: actual allocation support

39 internal results in twelve modules compile and pass independent closure
kernel checking (75861 exit 0). No public jet equivalence or coverage entry
is claimed. This is support for proving original simplicity_ge_negate against
the already ported literal ge_negate, not a numeric substitute specification.

The original affine object has size 88, X at 0, Y at 40, flag at 80. The new
run actually owns 88 bytes: do not use point theorems requiring 128 bytes as
premises, invent an offset free, or allocate extra bytes. Equality of symbolic
field cells permits reuse of the arithmetic bridge; ownership is separate.
The shared owned_field_slice_initial_rep is parameterized by actual enclosing
allocation size and derives representation from exact loads and whole-object
Freeable. It does not weaken any public theorem or claim arbitrary owner bases.

eval_affine_weak_reader_owned derives the original weak-normalizer call, exact
reader-produced field preservation, whole-object Freeable and outside-slice
framing, with six inherited execution assumptions. The load bridge and shared
representation proof print four inherited logical assumptions. The imported
kernel closure contains the unchanged fifteen context axioms; its unsafe
categories are empty. Distinguish closure imports from per-result dependencies.

eval_affine_negate_point_output now derives the entire original ge_neg helper
call: actual entry, 88-byte whole-struct self-copy, generated Y calls, return
and empty-local free. It preserves X, flag, whole-object Freeable and framing,
and derives exact negative Y storage. No execution, successful copy, output or
free is assumed. Shared load/foot transport is size-parameterized. Next compose
read_ge/ge_neg/write_ge and public 16+88 entry allocation/source copy/true return/
both frees. Reuse literal field bridges, not a replacement public formula.
Only after complete literal output and lifecycle should source gates, literal
parametricity, inventories, contracts/assumptions review and isolated acceptance
precede public registration. General frame/evaluator-domain review stays open.

Scratch: /tmp/jet-ge-negate.aFl8mr. Compiler Coq 8.17.1 (OCaml 4.14.4),
CompCert 3.14/VST 2.14. In /tmp/jet-negate-accept.ftWsqQ/Coq:

```sh
export PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH
ulimit -S -s 65520
bash build-jets.sh --coqc \
  -R /tmp/jet-gej-infinity.YrUC7w C \
  -R /tmp/jet-gej-predicate.W2FtCz C \
  -R /tmp/jet-gej-negate.IMImaX C \
  -R /tmp/jet-ge-negate.aFl8mr C \
  /tmp/jet-ge-negate.aFl8mr/jet_secp_affine_negate_call.v
```

Use --coqchk -silent -o with the same overlays and C.jet_secp_affine_negate_call
for the complete twelve-module kernel closure. Pin PATH in every invocation;
an unpinned slice-kernel attempt exited 1 because Rocq 9.3 cannot read 8.17
objects. Corrected slice kernel 77501 exited 0; original weak kernel 31133
and final owned closure 75855 exited 0. No failed run is counted as evidence.

Per-result preliminary assumption printing 99605 exited 0 in the scratch tree,
driver affine_assumptions_review.v, outputs assumptions-review.out/.err.
Inventory was extracted from all 39 actual source declarations in twelve
modules, not inferred from manifest counts. Read-only strict review passes:
39 exact reports, 22 closed, unchanged six-name union and final helper set,
empty diagnostics and all twelve compiled/archive hashes identical. Reproduce
with review-assumptions.py --work /tmp/jet-ge-negate.aFl8mr. See
ASSUMPTION-REVIEW.json. Kernel completion is separately recorded in
KERNEL-REVIEW.json. This is not
a complete public-contract or full acceptance receipt.

Use C.jets_secp (the normalized pinned translation unit), not the older
C.jets_secp256k1 AST with different composite identifiers. The actual helper
uses __6121 for affine storage and __5467 for field storage. Original source
ports/build configuration and canonical specs are unchanged.

Combined infinity/predicate full acceptance 24487 exited 0: 694 kernel modules,
3866 audited results/2013 closed, reviewed snapshots, negative tests and four
AST checks. See ../gej-predicate/COMBINED-ACCEPTANCE.json; not checkout or affine
acceptance. Point-negate
normal-load-path build 91913 has exited 0 separately. Its sequential full
snapshot generation 20895 is live; see ../gej-negate/NORMAL-BUILD-REVIEW.json.
Poll existing handles; do not restart or edit either candidate's proof or
metadata inputs while its check is running.
