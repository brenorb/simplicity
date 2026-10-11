# Affine negation: actual allocation support

28 internal results in nine modules compile and pass independent closure
kernel checking (78337 exit 0). No public jet equivalence or coverage entry
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

Actual magnitude-one field negation and both Y calls now retain X, flag and
88-byte ownership. Shared load/foot transport is size-parameterized. Next
derive the real 88-byte struct self-copy, then compose original
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
  /tmp/jet-ge-negate.aFl8mr/jet_secp_affine_weak_owned.v
```

Use --coqchk -silent -o with the same overlays and C.jet_secp_affine_weak_owned
for the complete four-module kernel closure. Pin PATH in every invocation;
an unpinned slice-kernel attempt exited 1 because Rocq 9.3 cannot read 8.17
objects. Corrected slice kernel 77501 exited 0; original weak kernel 31133
and final owned closure 75855 exited 0. No failed run is counted as evidence.

Combined infinity/predicate full acceptance 24487 is still live on frozen
inputs at the assumption gate after 694 kernel modules passed. Point-negate
normal-load-path build 91913 is also live separately. Poll existing handles;
do not restart or edit either candidate while its check is running.
