# Extended mixed-addition ratio: noncanonical equal-point Y

Status: implementation-to-specification mismatch formally established for the **unregistered**
`simplicity_gej_ge_add_ex` jet. Do not register an unrestricted equivalence theorem
or exclude the witness to make one pass. No target correction is made here.
The non-extended `simplicity_gej_ge_add` drops the ratio and is not contradicted.

## Expected versus actual

Let `p = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f`,
the secp256k1 field modulus. Use the five 256-bit input words
`A=((0,p),1)` and `B=(0,0)`, with disjoint valid input/output frames.

| Result | Ratio (first 256 of 1024 output bits) |
| --- | --- |
| Fixed literal Simplicity program | `p` |
| Original C jet, checked Clight execution | `0` |
| Original C jet, native execution | `0` |

`FE` is `Word256` in the fixed program, so `p` is a representable input;
the formal input type does not require a canonical field encoding. The point
is off curve, which is also not excluded by the public Word256 jet type.
The difference is an encoding/normalization difference, not a claim that
`p` and `0` denote different mathematical field elements.

The equal-point branch of `Haskell/Core/Simplicity/Programs/LibSecp256k1.hs`
`gej_add_ex` uses `oih &&& gej_double`: the ratio is the **original** Y word,
without a final `fe_normalize`. Both computed H and I are zero modulo p for
this input, and the incoming Z=1 is not infinity. Thus that ratio is `p`.
`gej_ge_add_ex` supplies affine Z=1 and retains this ratio.

In `C/jets-secp256k1.c`, `read_fe` normalizes the input `p` to zero. The
original `secp256k1_gej_double_var` copies Y into `rzr` and weak-normalizes it;
the public jet then calls `write_fe`, which normalizes before serializing.
The observed ratio is consequently zero. The C writer's established output
model cannot produce the noncanonical word `p` at all.

This is a real disagreement between the frozen sources. It does not establish
which source should be changed: that is a separate upstream decision. In
particular, changing the literal branch, changing C serialization, or adding
canonical-input restrictions would change this proof task's target.

## Evidence and limits

The complete diagnostic sources are in
[`proof-work/secp-ratio-mismatch`](../../proof-work/secp-ratio-mismatch/):

- `extended_ratio_witness.v.source` is a completed, separately compiled Coq
  witness, not an accepted jet theorem. `extended_ratio_equal_branch` reduces
  the exact literal tree. `extended_ratio_p_witness` proves the expected ratio's
  numeric value is p. It uses only inherited functional extensionality.
  `extended_ratio_p_not_writer_output` is closed and proves that no output of
  the established field-writer value model equals the word p.
- `probe.c` invokes the **original public C jet**, not a reimplementation or
  arithmetic simulator. Separate stack arrays contain 1280 input and 1024
  output bits. It checks successful return, full output-cursor advancement,
  and the observed zero ratio. An AY=0 control also returns zero.
- Both `-DRECKLESS` and a build without that define reproduced the result
  with Apple clang 21.0.0, arm64-apple-darwin27.0.0, AddressSanitizer and
  UndefinedBehaviorSanitizer; the runs exited zero without sanitizer findings.
  This does not assert equivalence of native builds to the pinned x86-64
  CompCert configuration.

The archived witness established the formal specification result and the
native discrepancy, but not whole-public Clight execution. That historical
verification limit is now superseded by
`jet_secp_mixed_ex_counterexample.gej_ge_add_ex_public_counterexample`.

For the exact input above and any environment argument, the ordinary Coq
theorem constructs a successful execution of the **original public Clight
function** and proves its resulting output memory cannot contain the fixed
literal program's encoded result. It establishes:

- existence of the original program's `Genv.init_mem`, using the existing
  checked initialization theorem;
- freshly allocated, disjoint 1280-bit input/1024-bit output frames, preserving
  all loads in the initial program memory and exposing their freshness;
- the actual public function entry and four local allocations of sizes
  16/128/88/40, the by-value source-frame copy and the original ratio clear;
- both actual readers, the original non-NULL mixed-addition helper, both
  writers in their original order, successful return and all local frees;
- a fully consumed output cursor, a zero numeric ratio, and a first output bit
  of false, whereas the literal specification's first bit is true.

The final counterexample has no intermediate-execution, H/I-test, caller,
canonical-input or libc-model premise. Both H/I conditions and the finite-Z
condition are discharged for the witness. The result retains the six inherited
assumptions; the pure bit disagreement is proved separately. Normal compilation,
recursive kernel checking, and reviewed no-update assumption/contract checks
passed for the ordinary counterexample and its public-call modules. This is negative
correspondence evidence, not positive jet coverage: accepted coverage remains
505/533 and this jet remains unresolved.

The implementation proof reuses the original non-NULL doubling result in
`jet_secp_double_var_ratio.v`, the H/I arithmetic and equal-point dispatch in
`jet_secp_mixed_equal_ratio.v`, and the complete helper lifecycle in
`jet_secp_mixed_ratio_function.v`. The shared point writer now supports an
already-written prefix, leaving its old empty-prefix contracts intact.
`jet_secp_mixed_ex_public_{body,entry,prepare,rest,call}.v` discharges the
public wrapper. Y in these helper contracts is the reader-produced five-limb
field value: for public AY=p, that value is zero, not the untouched word p.

The formal execution is for the pinned x86-64 Clight program and its recorded
RECKLESS generation configuration. It is not an assertion-enabled Clight
proof, a proof of reachability through the full evaluator, or a native-machine
code refinement theorem. Native sanitizer observations remain separate.
The original six-assumption counterexample theorem exhibits a disagreeing
successful execution; it does not itself state `~secp_jet_local_spec`.
The separate theorem
`jet_secp_mixed_ex_refutation.gej_ge_add_ex_not_literal_local_spec` now proves
that negation for the fixed function, full input/output types and literal
program. It reuses the existing `jet_clight_determinism.eval_funcall_unique`:
any execution promised by the putative contract must have the very same final
memory as the checked disagreeing execution, contradicting its output cells.

The stronger refutation uses eight inherited assumptions: the counterexample's
six plus CompCert's standing `Events.external_functions_properties` and
`Events.inline_assembly_properties`, used by the existing general determinism
proof. No new axiom, counting contract or library-behavior model is declared.
The original six-assumption counterexample is unchanged. Keep these two
statements and their assumption sets distinct. Normal compilation, recursive
kernel checking and reviewed no-update assumption/contract checks passed for
the separate refutation module as well.

Consequently, 533/533 unrestricted equivalence contracts cannot be obtained
with this function, its literal target and the full input type all fixed.
This is a proved obstruction, not just a missing tactic. A target correction
requires separate explicit approval; unaffected proof work remains in scope.
No production C, original specification, API contract or generation setting
is corrected or narrowed here. Which target should change remains a separate
upstream decision.

On `070782b0`, the ordinary rebuild of the existing public negate, rescale,
double, projective-addition, mixed-addition, projective-equivalence and
mixed-equivalence modules passed serially, and their seven no-update
assumption/contract snapshots matched. This checks regression of those public
proofs after the shared prefix-writer refactoring; it is not a full acceptance
run for all 533 declarations.
The production C and canonical Haskell were unchanged in the proof commit
`63aa1380`; the existing 240-file source/configuration fidelity gate passed.
This discrepancy is not caused by a production/specification edit made for
the new mixed-addition proofs.

## Reproduction

From the repository root on the tested macOS host:

```sh
cc -O1 -g -DRECKLESS -ffunction-sections -fdata-sections \
  -fsanitize=address,undefined -I C proof-work/secp-ratio-mismatch/probe.c \
  C/frame.c C/jets-secp256k1.c -Wl,-dead_strip -o /tmp/secp-ratio-probe
/tmp/secp-ratio-probe
```

Repeat without `-DRECKLESS` for the second tested configuration. Expected
observations are `returned=1`, `remaining=0`, and 64 zero hex digits for both
the AY=0 control and AY=p witness. The literal program instead returns the
64-hex-digit word p for the latter.

With the repository's baseline Coq 8.17.1 and prepared proof dependencies,
the ordinary whole-public proof is reproduced by:

```sh
JET_TARGETS=C/jet_secp_mixed_ex_counterexample.vo bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_ex_counterexample
```

The separate existential-contract refutation is reproduced by:

```sh
JET_TARGETS=C/jet_secp_mixed_ex_refutation.vo bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_ex_refutation
```

The original archived literal-only witness remains reproducible separately:

```sh
JET_TARGETS=C/jet_secp_mixed_dispatch_literal.vo bash Coq/build-jets.sh -j2
ratio_check_dir=$(mktemp -d /tmp/secp-ratio-witness.XXXXXX)
cp proof-work/secp-ratio-mismatch/extended_ratio_witness.v.source \
  "$ratio_check_dir/extended_ratio_witness.v"
bash Coq/build-jets.sh --coqc -q -Q "$ratio_check_dir" RatioMismatch \
  "$ratio_check_dir/extended_ratio_witness.v"
```

The archive keeps this negative correspondence evidence separate from
positive jet registrations; it does not increase coverage.

## Worst-case implication

Consumers that normalize the ratio before using it as a field element may
not distinguish the results. Consumers that compare or hash its 256 output
bits can distinguish them. In the worst case, a program that asserts the
literal ratio equals p could succeed under the unjetted specification and
fail under this C jet, undermining semantics-preserving jet replacement.
No deployed consensus divergence, transaction exploit, memory-safety failure,
or asset loss has been demonstrated here. Such reachability and impact would
need a separate investigation; the native sanitizer runs alone do not prove
their absence.
