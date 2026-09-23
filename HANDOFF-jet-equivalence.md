# Handoff: next complete arithmetic jet proof

Reviewed by Astra on 2026-09-23 for Luna High. Work locally on
`feat/jet-equivalence`, with small checked commits and no push. Read
[/Users/brenorb/.codex/skills/coq-proof-engineering/SKILL.md](/Users/brenorb/.codex/skills/coq-proof-engineering/SKILL.md)
and its Clight reference before proof work.

## Objective and current status

Prove execution of the **actual C library jet**, represented by the generated
CompCert Clight body, returns the result of its canonical primitive Simplicity
program. Mathematical correctness of an arithmetic specification is only a
bridge used inside that proof. No admits, new proof axioms, unchecked casts,
assumed helper executions, or successful-store premises in public jet theorems.

The broader user-approved objective still includes unrestricted initialized
output contents, arbitrary unrelated input bits, valid non-wrapping cursors
and crossings, the intended assertion configuration, and more arithmetic jets.
Much of this is already done. Do not restart the byte work or toolchain setup.

The app goal was **paused** when inspected for this review. This file does not
resume it or mark it complete. The old goal text's automatic delegation rule
is obsolete; later user instructions allow occasional strategy guidance.
Astra's current assignment is this review and handoff, not completing all
remaining wider jets in this turn.

| Checked source result | Actual scope |
| --- | --- |
| `jet_one8_layout.v`, `jet_increment8_layout.v`, `jet_add8_layout.v` | Complete individual jet calls under arbitrary non-wrapping input/output layouts, including crossings, with initial-memory contracts. |
| `jet_one_wide_layout.v:eval_one_wide_layout_matches_spec` | Complete `one_16`, `one_32`, `one_64` calls, selected by `W16/W32/W64`. |
| `jet_write_wide_layout_total.v:eval_write_wide_layout` | Actual 16/32/64-bit writers for every long payload, with stores constructed from permissions, output observation, prefix/range/permission preservation. |
| `jet_read16_layout_exec.v:eval_read16_layout_non_crossing` | Actual `read16` for arbitrary addresses/word indices and `cursor mod 64 <= 48`; still assumes a successful final cursor store. |
| `jet_read16_layout_exec.v:eval_read16_layout_crossing` | Actual `read16` for arbitrary addresses/word indices and all crossing remainders 49..63; assumes two cursor stores, deriving the intermediate backing load. |
| `jet_input_layout.v:frame_input_word_at` | Logical MSB-first input representation, independent of the C extraction algorithm. Its connection to `read16` is not yet proved. |

These are Clight2 terminating big-step execution results in `ge0` for the
committed generated program. They do not yet prove evaluator-wide substitution,
small-step uniqueness, or machine-code correctness of a built library.
Destination descriptors and their backing words occupy distinct CompCert
blocks. Do not advertise same-block disjoint layouts or other ABIs.

The C/AST configuration is **x86-64 Linux LP64, little endian, PRODUCTION**:
ordinary/static assertions are enabled; production debug-assert guards are
false. It is not the old RECKLESS configuration. Fully debug-enabled execution
is a separate unproved configuration. Generation uses the real C sources and
pinned Debian headers; see [JET_PROOFS.md](Coq/C/JET_PROOFS.md) for provenance.

## Review corrections and checkpoint

The old handoff repeatedly claimed there were no unfinished proofs, omitted
the general non-crossing reader, and called the goal active. At review start,
an uncompiled `eval_read16_layout_crossing` experiment was appended to the
reader source, with `Set Ltac Debug` enabled. Earlier accepted arithmetic
prefixes did not establish that theorem.

The interrupted diff is recoverable at
`/tmp/simplicity-handoff-review.3oJwDG/read16-crossing-unverified.patch`.
It is the **unverified original experiment**, superseded by the checked fixes
in this review; do not reapply it. The user's
separate untracked `jet-proof-review.patch` is untouched and must not be staged.

The old default build targeted only `check_jet_assumptions.vo`; that module
did not import `jet_read16_layout_exec`. Merely listing a file in
`_CoqProject.jets` did not put it in that target's dependency closure.
The build now checks **all listed modules**, and the audit explicitly imports
the W16 reader and prints its execution assumptions. New public results should
also be added to the audit. `Print Assumptions` prints a report; it is not an
automated rejection of unexpected axioms.

The general crossing theorem now closes with `Qed`. The review fixed the
true unsigned comparison through a small explicit semantic lemma, prevented
eager temporary lookup reduction from expanding symbolic widths, supplied
both shift guards, proved the next-pointer equality and intermediate cursor
load, and made the return formula use the same remainder normal form as its
arithmetic hypotheses. Both general reader branches still need a total
initial-memory contract and the logical representation bridge. Validation
and the exact post-review reader checkpoint are recorded below.

## Next milestone: complete increment_16, then add_16

The architecture is appropriate. The execution tactic feedback and order of
integration were the main productivity problems. Both raw W16 reader branches
are now available; stop generalizing raw reader execution and compose them
into a useful public result.

1. **Construct the reader memories from initial permissions.** Use the two
   checked raw kernels and copy the structure of `eval_read8_layout`.
   Derive stores and intervening loads, return advanced fields and precise
   load/permission/valid-block preservation. No logical-bit algebra is needed
   for this first layer.
2. **Connect the result to the logical Word16 input.** Prove exact unsigned
   value equality from `frame_input_word_at`, separately for each extraction
   formula. Compose this bridge with the total reader contract.
3. **Compose carry-plus-wide output and the actual increment_16 body.**
   Prove symbolic carry/value correspondence, use the existing bit/wide
   writers, and include source-frame allocation/copy/free. The acceptance
   result covers every Word16 input, all valid input/output alignments,
   arbitrary unused input bits and arbitrary initialized output contents.
4. **Prove add_16 with two consecutive reads.** Preserve the remaining input
   slice across the first cursor store. Reuse the carry/output contract and
   symbolic `Word.adder_correct` bridge.
5. Only then extend increment/add to 32/64.

If the crossing representation bridge stalls, first commit a complete
`increment_16` theorem for non-crossing input and arbitrary output alignment.
That is a clearly labeled intermediate milestone, not a replacement for the
accepted all-alignment goal. It lets arithmetic and function-boundary work
advance without another sequence of isolated reader-only commits. Do not
build more fixed-value/cursor kernels.

### Reuse strategy across widths

Use the increment_8/add_8 proof architecture, extracting shared lemmas rather
than duplicating their complete developments for each width. Parameterize
Simplicity programs by the word index n and arithmetic/bit slices by the bit
width w = 2^n; these are different parameters (Word16 is Word 4).

- **Frame lifecycle:** reuse source allocation/copy/free, initial-permission
  store construction, and memory preservation. The existing function-entry
  and frame-copy lemmas already handle much of this independently of width.
- **Arithmetic/specifications:** parameterize the canonical increment/add
  programs and prove carry/payload correspondence using modulus 2^w and
  Word's symbolic arithmetic lemmas. Follow `jet_add8_word.v`, not the older
  exhaustive increment_8 bridge. Replacing that byte bridge can follow once
  the shared proof works; it need not delay the W16 milestone.
- **Output composition:** generalize carry-plus-byte to carry-plus-word,
  consuming w+1 writable cells and reusing the already checked wide writers.
- **C execution:** retain small adapters for the actual generated reader and
  jet bodies at each width. Shared arithmetic lemmas alone do not establish
  execution of those functions.

Keep the ABI differences explicit: read8 returns `Vint`, while the generated
16/32/64-bit readers return `Vlong`. For 16/32-bit inputs the sums fit in the
64-bit carrier; 64-bit increment/add may wrap that carrier. Use modular sum
semantics for that case, with the separately computed carry, rather than
assuming the unsigned machine sum always equals the unbounded integer sum.

Validate this factoring through complete increment_16 and add_16 results,
then instantiate or extend it for 32/64. Avoid a large framework refactor
before those two concrete consumers demonstrate which lemmas are shared.

### Reader interface: settle this before writing another large tactic

A proposed `eval_read16_word_at` should consume:

- `frame_base_valid base` and `frame_fields_at m bf base bw edge cursor`;
- `frame_input_word_at m bw edge cursor x`, where `x : tySem (Word 4)`;
- `0 <= cursor <= Int64.max_unsigned - 16`;
- `Mem.valid_access m Mint64 bf (base + 8) Writable` and `bf <> bw`.

It should return an existential memory `mf` and payload `r`, with the actual
`f_simplicity_read16` call returning `Vlong r`, and:

- **`Int64.unsigned r = @toZ (WordToZ 4) x`**;
- final descriptor fields at `cursor + 16`;
- unchanged loads outside the eight-byte cursor field;
- preservation of permissions and valid blocks.

The exact value equality gives `0 <= unsigned r < 65536`. Equality merely
after `decode_wide W16` is insufficient: decoding discards high bits but
the C carry comparison does not.

`frame_input_word_at` describes backing bits only. It does not supply frame
fields, descriptor permissions, separation, or final-cursor representability.
Sixteen valid bit positions give at most `cursor + 15 <= max_unsigned`;
the last cursor update needs `cursor + 16 <= max_unsigned`. State the latter
explicitly. The caller's original source descriptor need not be writable:
the jet copies it into a fresh writable local block before reading.

To bridge the representation, first prove indexed lookup for
`frame_input_word_bits`. Word16 is `Word 4` (Word n has 2^n bits).
For each `0 <= i < 16`, the expected bit is `testbit (toZ x) (15-i)`.
On the non-crossing path, `(cursor+i)/64 = cursor/64` and
`(cursor+i) mod 64 = cursor mod 64+i`. The bit at index zero supplies the
high-word load; other witnesses for that same load are equal by determinism
of `Mem.load`. Use `Int64.bits_zero_ext`, `Int64.bits_shru`, range facts
and bit extensionality to prove the exact value. On crossings, split input
indices at k: indices below k are in the high word, the rest in the preceding
word. Index k supplies the second-word load. Use quotient/remainder identities
and load determinism for all other bit witnesses. Prove high result bits are
zero; do not stop at equality of its sixteen low bits. Keep payloads symbolic.

Use `jet_read8_layout_total.v` for store/permission/range preservation and
`jet_input_layout.v` for logical input preservation. Do not redefine the
logical input predicate to mean “the C extraction result is x”; prove the
representation bridge.

### Output and arithmetic: work missing from the old reader-only plan

`eval_write_wide_layout W16` writes sixteen bits, but increment needs a
carry **and** sixteen bits. Generalize the structure of
`jet_carry_byte_layout.v:eval_carry_byte_layout` to carry-plus-wide output.
Reuse `write_frame_at_after_bit` (already count-parametric), the total bit
writer and total wide writer. Preserve the carry when the payload write
touches the same word, and when the carry was the last bit of the previous
word. Reuse `write_layout_previous_inside/boundary`. The postcondition uses
cursor `cursor-17`, written-prefix preservation and the union of modified
ranges. `slice_output_at`/`slice_write_low` already expose the word payload.

Inspect `f_simplicity_increment_16` in `jets.v` and `INCREMENT_` in
`C/jets.c`. Under LP64 the input, sum and writer argument are **64-bit
unsigned long**, not a 16-bit C integer. For input 65535, the sum passed to
the writer is 65536; the writer's 16-bit observation discards the high bit.
The carry is the unsigned comparison `65534 < x`.

Define the canonical width-16 increment program by the same composition as
`increment8_spec`: `true &&& iden >>> full_increment`, with
`full_increment = oh &&& (ih &&& (unit >>> zero)) >>> full_add`.
The source is `Haskell/Core/Simplicity/Programs/Arith.hs`.
Use `Word.fullAdder_correct`, `Word.zero_correct`, pair `toZ` and
`from_toZ`/injectivity to prove carry and low-word equality symbolically.
The existing `jet_add8_word.v` is the arithmetic model; do not enumerate
65,536 increment inputs or input pairs. Prove parametricity/monadic
interpretation as for the existing specifications.

For the complete call, use `jet_increment8_layout.v` and
`jet_increment8_layout_exec.v` as templates. Reuse `entry_frame_jet`,
`exec_frame_jet_copy`, `call_frame_writer_cast`, frame-copy preservation
and the dynamic reader symbol/function lookup lemmas in `jet_wide.v`.
Read the actual AST temporary names/types. Preserve input/output backing
aliasing already allowed by the existing proofs; the fresh local descriptor
provides the separation needed by the reader. Do not add blanket pairwise
block inequality assumptions for convenience.

### Crossing execution: solved obligations and lessons to preserve

For `r = cursor mod 64 > 48`, choose `k = 64-r` and `t = r-48 = 16-k`.
Then `1 <= k,t <= 15`. The C body does:

1. Load high at `edge-8*(1+cursor/64)`; keep its low k bits and shift by t.
2. Store local cursor `cursor+k`; set n to t, frame_shift to 64, and decrement
   the backing pointer by eight bytes.
3. Test the generated constant `UWORD_BIT < n`; it is false because t < 16.
4. Load low at `edge-8*(2+cursor/64)`; shift right by `64-t`, keep t bits,
   OR with the high contribution, and store final cursor `cursor+16`.

In particular, the code assigns frame_shift = 64 directly. It does not
recompute cursor division/modulo after the first store. The while condition
uses the generated constant, not the `_frame_shift` temporary.

The checked code consistently uses `k = 64-r` and `t = r-48` in its
arithmetic facts and return formula. The interrupted attempt mixed `r-48`
with `16-(64-r)`; arithmetic equality is not definitional equality. Keep a
single normal form when composing the representation bridge.

These execution obligations are now discharged in the source:

- unsigned comparison semantics for the true first branch and false loop;
- both shift guards: shift counts strictly less than 64;
- next-pointer equality after subtracting eight bytes;
- `Mem.load_store_same` for the cursor in the intermediate memory;
- preservation of the low backing-word load across that cursor store.

The interrupted candidate omitted the next-pointer equality and intermediate
cursor-load fact; both are now supplied. The remaining obligation is exact
bit-slice/range interpretation of the result, not another execution replay.
A bounded 15-case split on k is an acceptable fallback for closed scalar obligations;
never enumerate payloads or unfold symbolic memory with `vm_compute`.

## Feedback loop and reproducible commands

From the repository root, define a shell helper for the existing environment:

```sh
jet_coq() {
  env OPAMROOT=/Users/brenorb/.opam-simplicity-root \
    COMPCERT=/tmp/simplicity-compcert VST=/tmp/simplicity-vst \
    opam exec --switch=simplicity -- bash Coq/build-jets.sh "$@"
}
jet_coq -j2
jet_coq --coqc -q C/jet_read16_layout_exec.v
jet_coq --coqtop -quiet
jet_coq --coqchk -silent C.jet_read16_layout_exec
```

Coq is 8.17.1, CompCert 3.14, VST 2.14. The three direct modes reuse the
project load paths and change directory to Coq. They do not rebuild imports.
Use the normal build after dependency changes, direct `--coqc` for short
iterations once dependencies are current, and `--coqchk` after the completed
module builds. Never add `-q` to coqchk. Do not recursively map /tmp.

After a tactic failure, expose the first unfinished leaf goal and its evars.
Wrapping the entire recursive `read16_cross_stmt` in `try` rolls back all
progress when a deep leaf fails, so `Show` then displays the whole AST and
reveals little. Step through statement constructors, or use a one-step
tactic that leaves the failed leaf visible. Inspect comparison/shift semantics
in installed `Cop.v`; arithmetic equalities do not prove the shift guard.

After two attempts at the same failure without a new diagnosis, change the
decomposition. Use explicit, small expression lemmas before retrying a body.
A `first` branch can succeed with unresolved goals; use `solve` when closure
is required. Give speculative tactics roughly ten-second deadlines. Keep
`Int64` operations symbolic and isolate generated constants.

Do not edit a source while it is compiling or launch duplicate compilers.
Changes to foundational modules can trigger several minutes in `jet_exec.v`
and `jet_write8.v`; that is not a reason to repeat the same build. Keep the
process id and wait. A stale .vo is not evidence about the current .v.

At each public milestone, build all listed modules, inspect the assumption
report, and run coqchk on the new public module. Execution inherits the
documented CompCert axioms/external-semantics parameters; no new proof
assumptions should appear. Pure arithmetic/representation bridges should
be closed under the global context. AST regeneration is only needed if its
inputs change; do not reinstall tools or edit generated bodies for this task.

## Review validation

- `6a646ad`: general crossing reader, closed with `Qed`; direct `coqc`
  and independent `coqchk -silent C.jet_read16_layout_exec` passed (exit 0).
  The last declaration is `eval_read16_layout_crossing`. No unfinished
  crossing theorem or debug tactic remains in the source.
- Shell syntax and the new `--coqtop` mode passed.
- The full `build-jets.sh -j2` build, now covering every listed module and the
  updated assumption audit, passed (exit 0). The new reader results report
  only the same six inherited assumptions/parameters: `classic`,
  `functional_extensionality_dep`, `sig_not_dec`, `sig_forall_dec`,
  `external_functions_sem`, and `inline_assembly_sem`.
- No admits, aborted proofs, new axiom declarations or unchecked-cast escapes
  were found in the jet proof sources. `git diff --check` passed.

The broader goal remains unfinished and paused. The next work is the reader
contract based on initial memory, its exact logical-word bridge, and complete
`increment_16`; there is no remaining raw crossing execution failure to debug.
