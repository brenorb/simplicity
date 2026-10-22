# Extended mixed-addition ratio: noncanonical equal-point Y

Status: implementation-to-specification mismatch observed for the **unregistered**
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

These establish a formal specification result plus a native C discrepancy.
They are **not** a completed Clight execution counterexample for the whole
public extended jet. The latter remains a verification limit, not an assumed
premise or a reason to narrow the requested input domain.

The ordinary proof module `jet_secp_double_var_ratio.v` now proves the complete
original `secp256k1_gej_double_var` call with a non-NULL ratio pointer on the
finite-point path and positioned Y limbs (including public-reader outputs).
It derives the actual struct copy, weak normalization, point doubling, Z test
and flag store from owned storage, preserving the separate ratio field and
both objects' ownership. No intermediate execution or libc model is assumed.
The common post-ratio suffix is shared with the existing NULL-ratio proof.
Normal compilation and recursive kernel checking passed; the execution result
retains the six inherited assumptions. Reproduce this helper check with:

```sh
JET_TARGETS=C/jet_secp_double_var_ratio.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_double_var_ratio
```

`jet_secp_mixed_equal_ratio.v` composes that doubling result with the actual
mixed-addition arithmetic prefix, both H/I tests and the equal-point return.
`jet_secp_mixed_ratio_function.v` closes the complete original
`secp256k1_gej_add_ge_var` call on this path, including all ten actual local
allocations and frees. From positioned initial X/Y, bounded Z/affine
coordinates and H=I=0 modulo p, it derives the final point, exact ratio Y,
all three caller-owned objects and external framing. The ratio destination
may initially be uninitialized. The original helper's environment, entry
allocation derivation and free-list ordering are reused; no intermediate
call is a premise of the complete result. Here Y is the initial five-limb
field value, not the untouched public input word AY: the public reader
normalizes AY=p to zero before this helper is called. Normal compilation,
recursive kernel checking and reviewed no-update assumption/contract checks
passed for both modules, retaining the same six inherited assumptions.

This is **not yet the whole-public counterexample**. Remaining composition:
the extended public wrapper's readers and ratio/point writers, and a concrete
valid-frame instantiation for the witness above. The helpers' positioned-Y
premise is not a proposed restriction on the public jet's input type.

Reproduce the complete helper's normal and recursive kernel checks with:

```sh
JET_TARGETS=C/jet_secp_mixed_ratio_function.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_ratio_function
```

For the remaining public composition, reuse `eval_mixed_public_reads` (its
output-capacity parameter already permits 1024 bits) and the owned field
writer with size 40 for the ratio. The public AST allocates src/point/affine/
ratio objects of sizes 16/128/88/40, clears the ratio before reading, then
writes the ratio before the point. Extend the existing three-coordinate
writer to an already-written prefix, as done for the affine writer; do not
reorder the actual calls. `jet_frames_constructible` can instantiate disjoint
1280-bit input/1024-bit output frames after the wrapper is proved.

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

With the repository's baseline Coq 8.17.1 and prepared proof dependencies:

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
