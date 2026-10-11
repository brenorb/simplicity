# Affine negation: actual allocation support

109 results in thirty-eight modules compile and pass independent public closure
kernel checking (98418 exit 0). ge_negate_literal_local_spec proves original
simplicity_ge_negate against the literal canonical Simplicity ge_negate under
the unchanged inherited local-frame contract, for arbitrary Word256 pairs.
No coverage entry, full isolated acceptance or general evaluator-domain result
is claimed.

Newest public milestone: shared lifecycle/setup lemmas parameterized by actual
owned object type and size; exact public 16+88 entry/generated call tree;
derived read_ge/ge_neg/write_ge remainder; actual source copy, true return
and both frees; final literal local-spec theorem. Compiler sessions 13581,
88693,94499,50379,18181,73283 all exited 0. Independent public plus inherited
literal-parametricity closure 98418 exited 0 with the same fifteen imported
context axioms and empty unsafe categories. Per-result 109-print 53162 exited
0; strict review passes: 109 actual reports, 54 closed, unchanged six-name union,
exact final public/helper/reader/writer sets, all 91 older sets unchanged, empty
diagnostics and exact 38-source hashes/declaration inventories. Reproduce with
review-assumptions.py --work /tmp/jet-ge-negate.aFl8mr; receipt
PUBLIC-ASSUMPTION-REVIEW.json. The 91-result audit below is historical.

Source correspondence gate plus 53 mutation fixtures pass separately. They are
supplemental, not a compiler/kernel or transitive source-fidelity certificate.
Next audit all 109 actual result dependencies, review exact type/definition
contracts and canonical ports, then assemble a normal-load-path isolated
candidate, review full snapshots and run full acceptance. Do not register the
jet merely because this checked public theorem now exists.

Boundary engineering correction: inversion on a pair containing a large Clight
function record timed out while decomposing its implementation. Applying
f_equal to fst/snd extracts only the identifier/function equalities; explicit
secp_symbol_block gives the witness. It passes with the original ten-second
limit and unchanged target. Incomplete Show scratch was never compiled/counted.

Newest milestone: actual-size original field writer, other-coordinate and
outside-owner framing, both original affine writes, complete write_ge entry/
body/return/empty-local free, and literal ge_negate output bridge all compile.
All 22 new results reuse point-field arithmetic while preserving real ownership
size 88; no 128-byte point ownership is assumed. Compiler sessions: run 7849,
execution 78252, field adapter 71827, preservation 91818, two writes 64947,
body 33230, complete writer 92175, literal bridge 66203, all exit 0. Independent
three-target closure kernel 10648 exited 0 with unchanged fifteen context axioms
and empty unsafe categories. Print driver affine_assumptions_review_91.v
finished in session 17087 with exit 0. Strict review passes for all 91 actual
reports, 48 closed, unchanged six-name union, exact final reader/helper/writer
sets, all 69 inherited sets unchanged and empty diagnostics. All thirty-two
archived/materialized source hashes match actual declaration inventories.
Reproduce with review-assumptions.py --work /tmp/jet-ge-negate.aFl8mr; receipt
WRITER-ASSUMPTION-REVIEW.json. Older 69-result audit below is historical.

The first field-adapter attempt timed out while inferring all arguments through
eapply. Interactive Show confirmed that all five limb bounds, field loads and
actual ownership were already present. Applying eval_owned_wide_write_fe with
explicit size, limbs, memories and the established initial representation
avoids expensive inference; no timeout increase or contract change was needed.
The literal-step proof explicitly unfolds its program: do not mark that program
opaque before this one-step proof. Debug Show files were never compiled/counted.
Next compose read_ge/ge_neg/write_ge in the original public remainder, then
prove actual 16+88 entry/source copy/true return/both frees against the literal
target. No public coverage yet.

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
free is assumed. eval_read_ge_canonical_fields now derives the entire original
affine reader: entry, both reads, real zero-flag store, exact canonical X/Y,
source cursor advancement by 512, 88/16-byte ownership, framing and return.
The shared original field reader is parameterized by enclosing allocation
size; concrete fit inequalities are discharged for the affine 88-byte layout.
Shared load/foot transport is also size-parameterized. Next derive write_ge,
then compose read_ge/ge_neg/write_ge and public 16+88 entry/source copy/true return/
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
  /tmp/jet-ge-negate.aFl8mr/jet_secp_read_ge_fields.v
```

Use --coqchk -silent -o with the same overlays and C.jet_secp_affine_negate_call,
C.jet_secp_read_ge_fields and C.jet_secp_write_ge_negated_literal for the complete
thirty-two-module joint closure.
Pin PATH in every invocation;
an unpinned slice-kernel attempt exited 1 because Rocq 9.3 cannot read 8.17
objects. Corrected slice kernel 77501 exited 0; original weak kernel 31133
and final owned closure 75855 exited 0. No failed run is counted as evidence.

Per-result preliminary assumption printing 31866 exited 0 in the scratch tree,
driver affine_assumptions_review_69.v, outputs assumptions-69-review.out/.err.
Inventory was extracted from all 69 actual source declarations in twenty-four
modules, not inferred from manifest counts. Read-only strict review passes:
69 exact reports, 38 closed, unchanged six-name union and final helper/reader sets,
all 39 inherited helper sets unchanged, empty diagnostics and all twenty-four
compiled/archive hashes identical. Reproduce
with review-assumptions.py --work /tmp/jet-ge-negate.aFl8mr. See
READER-ASSUMPTION-REVIEW.json (the older ASSUMPTION-REVIEW.json records the 39-result
checkpoint). Kernel completion is separately recorded in
KERNEL-REVIEW.json. This is not
a complete public-contract or full acceptance receipt.

Proof-engineering diagnosis: the first full-reader compile stopped at an
uninstantiated enclosing-size existential in owned_field_load_transport.
The interactive goal was offset+40 <= ?size (not a missing mathematical fact).
Supplying offset, actual size 88 and the current memories explicitly closes
the proof without changing its preconditions. The incomplete Show scratch
was never compiled or counted. Final compiler 99590 exited 0.

Use C.jets_secp (the normalized pinned translation unit), not the older
C.jets_secp256k1 AST with different composite identifiers. The actual helper
uses __6121 for affine storage and __5467 for field storage. Original source
ports/build configuration and canonical specs are unchanged.

Combined infinity/predicate full acceptance 24487 exited 0: 694 kernel modules,
3866 audited results/2013 closed, reviewed snapshots, negative tests and four
AST checks. See ../gej-predicate/COMBINED-ACCEPTANCE.json; not checkout or affine
acceptance. Point-negate
normal-load-path build 91913 has exited 0 separately. Its sequential full
snapshot generation 20895 has exited 0; see ../gej-negate/NORMAL-BUILD-REVIEW.json.
Full inherited/new snapshot review now passes; full isolated point-negate
acceptance 77601 is live at point-negate-full-acceptance.log. No terminal
acceptance is claimed. See ../gej-negate/ACCEPTANCE-RUN.json.
Poll existing handles; do not restart or edit either candidate's proof or
metadata inputs while its check is running.
