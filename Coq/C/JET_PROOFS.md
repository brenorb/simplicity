# C jet implementation-to-Simplicity proofs

Coq proofs that the generated CompCert Clight of twelve jets of the C library
(`C/jets.c`, `C/frame.c`) computes what the corresponding Simplicity expression
computes, and that a call can replace the Bit Machine translation of that
expression in a local, explicitly described context.

| Jet | Simplicity specification |
| --- | --- |
| `one_8`, `one_16`, `one_32`, `one_64` | `true >>> left_pad_low word1 wordN` |
| `increment_8`, `_16`, `_32`, `_64` | `true &&& iden >>> full_increment wordN` (`increment_word_spec`) |
| `add_8`, `_16`, `_32`, `_64` | `Word.adder` (`false &&& iden >>> full_add wordN`) |

Build and reproduction instructions are in [../JET_BUILD.md](../JET_BUILD.md).
Nothing here concerns jets outside this list, the C evaluator as a whole, or
machine code.

## What is proved

The results form four layers. Each names the module and theorem; the exact
statements are in the sources.

### 1. Generated Clight against Simplicity (value theorems)

`eval_<jet>_layout_matches_spec` in `jet_one8_layout.v`,
`jet_one_wide_layout.v` (`one_16/32/64`, selected by `W16/W32/W64`),
`jet_increment8_layout.v`, `jet_add8_layout.v`, `jet_increment{16,32,64}_layout.v`
and `jet_add{16,32,64}_layout.v`.

For the actual generated function body (`f_simplicity_<jet>`), a complete
`ClightBigstep.Clight2.eval_funcall` (parameters as temporaries,
`function_entry2`) exists that returns `true`, has an empty trace, and leaves
memory `mf` such that

* the output cells hold the result of the canonical specification evaluated with
  `Alg.CoreFunSem` (`byte_output_at`, `wide_output_at`, `carry_byte_output_at`,
  `carry_wide_output_at`);
* the final output cursor is the initial cursor minus the output size
  (`frame_fields_at mf ...`);
* the already-written prefix of the topmost touched word is preserved
  (`write_prefix_at`), and every load outside the destination frame item's cursor
  field and the modified word range is unchanged, including other locations of the
  same blocks.

Preconditions concern the **initial** memory only: the input frame item is a
16-byte, 8-aligned region with non-wrapping fields (`frame_base_valid`,
`frame_fields_at`), the represented input bits are readable at their word
locations for an arbitrary non-wrapping cursor (`byte_input_at`,
`frame_input_word_at`, with `read_cursor <= Int64.max_unsigned - N` for `N` input
bits), and the output frame is writable with enough remaining cells
(`write_frame_at`: 8 for `one_8`, 9 for 8-bit increment/add, `wide_bits + 1` for
wide increment/add). Reads and writes may cross 64-bit word boundaries; other
input bits and the initial output word contents are arbitrary. Every helper call,
allocation, structure copy, store, return conversion and deallocation is derived
inside the proof; no intermediate successful store is assumed.

These theorems are intentionally permissive about aliasing: they permit an output
frame that overlaps its own input, whose bits the jet may overwrite after reading
them. They therefore do **not** say the input cells are unchanged afterwards. The
input frame item is only copied (by the by-value parameter), so `bs` may equal
`bd`, and `bi` may equal `bw`; the only block separation required is between the
output frame item and its cell block (`write_frame_at` contains `bd <> bw`).

### 2. Canonical encoding of the memory observations

`jet_encoding.v` proves, independently of any reader or writer algorithm, that
the observations used by layer 1 agree with `Translate.encode`:

* `encode_word`: `encode x = map Some (frame_input_word_bits x)` for every
  `x : Word n`, so the encoding of a word is its bits, most significant first.
  Closed under the global context.
* Read side (`frame_input_cells_at`: cell `i` of a read frame starting at cursor
  `c` is bit `63 - (c+i) mod 64` of the word at `edge - 8*(1 + (c+i)/64)`):
  `frame_input_word_at_encode`, `frame_input_word_pair_encode` (paired operands),
  and, for the legacy byte predicates, `byte_slice_at_encode`,
  `byte_input_single_encode`, `byte_input_pair_encode`.
* Write side (`frame_output_cells_at`: the cell written `i` steps after a cursor
  at offset `c` is bit `(c-1-i) mod 64` of the word at `edge + 8*((c-1-i)/64)`):
  `slice_word_output_encode`, `wide_output_at_encode`, `byte_output_at_encode`,
  and for carry-plus-word results `carry_wide_output_encode`,
  `carry_byte_output_encode`.

Padding cells (`None`) only require that the physical bit exist, not a value.
The decode/extract algorithms of the C readers and writers appear only in the
bridges from the older predicates to these ones.

### 3. Local replacement in a represented context

`jet_bitmachine_rep.v` defines `bm_rep m L s`: memory `m` represents the Bit
Machine `RunState` `s` under the layout `L`. It matches the evaluator (`C/eval.c`),
which stores every frame's cells in one allocation (`cells_blk`) and every
`frameItem` in another (`frames_blk`), the frames of each stack occupying
disjoint regions of the shared block. For each frame it requires: the item holds
the edge pointer and the C cursor; the frame's words are initialized; and its
cells are observed as in layer 2, with

* read frames: `n = |prevData| + |nextData|` cells, `ROUND_UWORD(n)` words ending
  at the edge, offset `padding + |prevData|`, cells `rev prevData ++ nextData`
  after the padding (so the zipper is un-reversed and the offset increases);
* write frames: `n = |writeData| + writeEmpty` cells, words starting at the edge,
  offset `writeEmpty` (decreasing as cells are written), written cells
  `rev writeData` (so `writeData` is un-reversed), and **no constraint on the
  unwritten cells**, whose physical bits a C writer may clear.

`bm_separated L s` is the noninterference condition: the jet writes only the
output frame item's cursor field and the output frame's words, so every other
frame item and every other represented read or write frame must be disjoint from
them. The value theorems do not need this; the contextual corollaries do, because
the caller's read frame and every inactive frame are part of the final Bit Machine
state. `gap_buffer_separated` (in `jet_context.v`) derives it for the evaluator's
gap-buffer layouts: items in increasing slots of `frames`, cells in increasing
addresses of `cells`, read frames then the gap then write frames.

`bm_rep_after_write` proves that, under `bm_separated`, the jet's writes
re-establish `bm_rep` with the written cells prepended to the active write frame,
preserving the caller's read frame, the inactive frames and the written prefix,
and permitting any change to the unwritten cells below.

`jet_canonical.v` restates layer 1 for every jet as `jet_local_spec f A B spec`
(inputs and outputs are `Translate.encode` cells; `*_local_spec`). The value
theorems are used unchanged.

`jet_context.v:jet_context` combines `jet_local_spec` with
`Translate.Naive.translate_correct`: for a parametric Simplicity expression `t`
whose jet satisfies the spec, a memory representing
`fillContext ctx {encode a; newWriteFrame |B|}` (with `bm_separated` and write
permissions on the active write frame, `active_write_writable`) is carried by the
C call to a memory representing
`fillContext ctx {encode a; fullWriteFrame (encode (t a))}`, and the Bit Machine
translation of `t` reaches the same abstract state from the same start
(`s0 >>- t Naive.translate ->> s1`). `jet_canonical.v` instantiates it for all
twelve jets (`*_context`).

The premises are satisfiable in evaluator shape: `jet_layout_witness.v`
constructs, for arbitrary `a`, `z`, `w`, a two-allocation layout with an inactive
read frame holding `z`, the `increment_64` input `a`, a 65-cell output frame and
an inactive write frame holding `w`, proves `bm_rep`, `bm_separated` and the
permissions, and derives (`increment64_layout_witness_context`) that the call
terminates and the resulting memory represents the final state, still containing
the caller's `z` and `w` frames.

This layer is local to one jet call and one represented context. It does **not**
claim that the C evaluator maintains `bm_rep` between calls, that `bm_separated`
holds during an evaluation, or that the evaluator as a whole implements
`translate_correct`.

### 4. Execution guarantees at the call boundary

`jet_clight_determinism.v` proves determinism of CompCert 3.14 Clight small steps
with `function_entry2` (`step2_determ`) from the Clight rules and CompCert's
`external_call_determ`; no determinism axiom is added. It reuses
`ClightBigstep.eval_funcall_steps` (with `function_entry2`) to turn a silent
big-step call into a `starN` path and proves, for `Clight2.eval_funcall ge m fd
args E0 mf res`:

* `eval_funcall_unique`: any other terminating big-step call from the same state
  has the same trace, memory and result;
* `eval_funcall_call_boundary` (for every call continuation `k`): the small-step
  execution from `Callstate fd args k m` reaches `Returnstate res k mf` in `n`
  silent steps; any execution of fewer than `n` steps is silent, has not yet
  returned to `k`, and ends in a state with exactly one successor, which is
  silent (nothing is stuck and there is no alternative); any execution of at
  least `n` steps passes through `Returnstate res k mf`; and any infinite
  execution from the call state is the silent call followed by an infinite
  execution of the caller;
* `eval_funcall_Kstop_terminates` (empty continuation): the call has no infinite
  execution and every maximal finite execution ends in `Returnstate res Kstop mf`
  with no events.

This distinguishes uniqueness of terminating executions from safety and
termination of all maximal executions, and it is scoped to the call boundary:
after the return nothing is said about the caller. `jet_guarantees.v` combines it
with layers 1 and 3: `jet_local_spec_guarantees` and `jet_context_guarantees`, and
`<jet>_guarantees` for all twelve jets.

## Coverage

| Jet | Value theorem | Canonical / context | Call-boundary |
| --- | --- | --- | --- |
| `one_8` | `eval_one8_layout_matches_spec` | `one8_local_spec`, `one8_context` | `one8_guarantees` |
| `one_16/32/64` | `eval_one_wide_layout_matches_spec W16/W32/W64` | `one{16,32,64}_local_spec`, `_context` | `one{16,32,64}_guarantees` |
| `increment_8` | `eval_increment8_layout_matches_spec` | `increment8_local_spec`, `increment8_context` | `increment8_guarantees` |
| `add_8` | `eval_add8_layout_matches_spec` | `add8_local_spec`, `add8_context` | `add8_guarantees` |
| `increment_16/32/64` | `eval_increment{16,32,64}_layout_matches_spec` | `increment{16,32,64}_local_spec`, `_context` | `increment{16,32,64}_guarantees` |
| `add_16/32/64` | `eval_add{16,32,64}_layout_matches_spec` | `add{16,32,64}_local_spec`, `_context` | `add{16,32,64}_guarantees` |

All 16-, 32- and 64-bit increment/add value theorems are proved from initial-memory
contracts, including W16 (`eval_read16_layout_total` derives the reader's stores;
`eval_increment16_layout_matches_spec` and `eval_add16_layout_matches_spec` are the
public results). The arithmetic bridges are closed: `add{16,32,64}_values_denote_input`
and `increment{16,32,64}_values_denote_input` (the 64-bit ones account for machine
wraparound and the unsigned carry test `(UINT64_MAX - y) < x`; the 16- and 32-bit
ones for a wider carrier that truncates only when written), and the 8-bit
`increment8_output_denotes_spec`, `add8_values_denote_spec`.

## Target and configuration

x86-64, little-endian, LP64, glibc integer typedefs; the library's `PRODUCTION`
assertion mode (ordinary and static assertions enabled, debug assertions'
guards false: the `writeBit` proof executes the generated guard rather than
assuming it succeeds). The caller's environment argument is `Vundef`, which none
of these jets uses. Frames are 16-byte `frameItem`s: the edge pointer at offset 0,
the offset at offset 8. Other ABIs, fully debug-enabled execution, and jets wider
than 64 bits are not covered.

## Assumptions

Public theorems are checked with `coqchk` and their axiom sets are recorded in
`jet_assumptions.expected` and enforced by `../audit-jet-assumptions.sh` (see
[../JET_BUILD.md](../JET_BUILD.md)). All axioms are inherited; none is introduced
by this development, and there are no `Admitted` proofs.

* Coq standard library, appearing in every proof that touches Clight or
  `Simplicity.Alg`: `Classical_Prop.classic`,
  `FunctionalExtensionality.functional_extensionality_dep`,
  `ClassicalDedekindReals.sig_forall_dec`, `ClassicalDedekindReals.sig_not_dec`.
* CompCert's parameterized external-call and inline-assembly semantics
  (`Events.external_functions_sem`, `Events.inline_assembly_sem`), which occur in
  the Clight relation: the value theorems and their consequences.
* `Events.external_functions_properties` and `Events.inline_assembly_properties`,
  CompCert's axioms on those semantics, used by the determinism results and
  therefore by `jet_clight_determinism.v` and `jet_guarantees.v` (19 theorems).
* Closed under the global context: `encode_word`, `gap_buffer_separated` and the
  arithmetic bridges listed above.
* `coqchk` additionally reports library-level axioms of the loaded dependencies
  (VST `prop_ext`, proof irrelevance, `propositional_extensionality`,
  `Archi.win64`, and others); they are recorded in `jet_coqchk_axioms.expected`
  and are not used by the theorems' own `Print Assumptions`.

Internal execution lemmas keep successful-store premises: for example
`eval_read16_layout_non_crossing`/`_crossing` and the raw writer lemmas
`eval_writeBit_layout_raw`, `eval_write8_layout_*_raw` assume the final stores
succeed. That is legitimate because the public contracts discharge them from
initial permissions; they are not themselves public claims.

## Trust boundary of the C-to-AST step

`jets.v` is generated from the real C sources by `clightgen`; Coq checks facts
about that Clight program, not that it represents the C source. The check
`Coq/C/check-jets-generation.sh` regenerates it with pinned inputs and compares it
byte-for-byte with the committed artifact. See
[../JET_BUILD.md](../JET_BUILD.md) for the trust boundary and pins. The
regeneration was checked on macOS/arm64 with Apple clang as preprocessor; Linux
regeneration is exercised by the `jets-ast` CI job.

## Structure copies and VST

Clightgen's `-normalize -fstruct-passing` gives each jet a by-value `frameItem`
parameter `_src` and a local variable of the same name; the first statement is
`Sassign (Evar _src) (Etempvar _src)`, a struct copy (`assign_loc_copy`) into a
freshly allocated local, whose address is then passed to the readers. The proofs
therefore carry explicit preconditions for this copy (a readable, 8-aligned,
16-byte source, `Mem.loadbytes`/`frame_base_valid`, and the non-overlap that the
fresh block provides) and use `jet_frame_copy.v`, `jet_frame_copy_layout.v` to
show the copied fields equal the source's.

The proofs are direct Clight big-step proofs. VST 2.14 is used as a dependency for
the `sha` library that `Simplicity.Word` imports, and its Clight core semantics
(`veric/Clight_core.v`) is defined with the same `function_entry2` as the semantics
used here, so an integration is not ruled out. What it would require is a `funspec`
treatment of the struct-typed parameter (a pointer to caller storage copied by the
callee prologue), of the block layout predicates (`frame_base_valid`,
cursor/edge fields, disjoint regions in shared blocks) and a connection from a
VST postcondition to `jet_local_spec`. That work was not done; the direct proofs
keep block, offset and cursor arithmetic explicit and no VST specification of
these functions exists in this repository.

## Remaining boundaries

* Whole-evaluator correctness: nothing proves that every evaluator execution
  establishes `bm_rep`/`bm_separated` before a jet call, or that replacing
  translated code by jet calls is correct for whole programs.
* Machine code: correctness is for Clight, not for the code a C compiler emits.
* The C-to-AST step is checked by regeneration only.
* Other configurations: other targets, `PRODUCTION` off, wider jets.
* The Nix derivation (`coqJets`) and the CI workflow were not executed where this
  branch was prepared; the scripts they invoke were.

## Proof organization

Reusable decomposition (validated on every width): (1) express the logical input
as selected MSB-first frame bits; (2) prove the actual reader returns the exact
unsigned value (an exact equality or a range bound, since decoding modulo `2^w`
alone does not fix the upper bits that a later carry comparison reads) and
preserves the frame and memory; (3) prove a width-specific closed arithmetic
bridge from the actual C values to the canonical program; (4) adapt the generated
body with its exact temporaries and casts and compose reader, arithmetic, writer
and frame lifecycle; (5) state the public theorem only over initial memory.

Practical notes: generated reader results are `Vlong` for 16/32/64 bits and
`Vint` for `read8`; a 64-bit sum can wrap while sub-64-bit sums do not, so the
bridges keep the carrier arithmetic explicit; use one normal form for cursor
arithmetic; isolate closed shift counts from symbolic memory; do not reduce
symbolic memory or enumerate payload values; never treat a `.vo` from an earlier
run as evidence for the current `.v`.

Module map (all are built by `Coq/_CoqProject.jets`; the earlier position- and
crossing-specific modules are kept as regression tests and as dependencies of the
general results):

* Generated code and execution: `jets.v`, `jet_exec.v`, `jet_one8.v`,
  `jet_read8.v`, `jet_write8.v`, `jet_writeBit.v`, `jet_increment8.v`,
  `jet_add8.v`, `jet_wide.v`.
* Frame and layout contracts: `jet_frame_spec.v`, `jet_frame_layout.v`,
  `jet_frame_access.v`, `jet_frame_arith.v`, `jet_frame_constants.v`,
  `jet_frame_copy.v`, `jet_frame_copy_layout.v`, `jet_input_layout.v`,
  `jet_input_position.v`, `jet_output_layout.v`, `jet_output_layout_step.v`,
  `jet_output9.v`, `jet_output_slice.v`, `jet_two_word_input.v`.
* Bit algebra: `jet_word_bits.v`, `jet_word_decode.v`, `jet_word_position.v`,
  `jet_word_slice.v`, `jet_word_repr.v` (width-generic range and decoding facts,
  shared by the 16-, 32- and 64-bit readers and `jet_encoding.v`),
  `jet_LSBclear_width.v`, `jet_LSBkeep_width.v`.
* Readers: `jet_read8*.v`, `jet_read{16,32,64}_layout_exec.v`,
  `jet_read{16,32,64}_layout_total.v`, `jet_read{16,32,64}_input_word*.v`.
* Writers: `jet_write*_layout*.v`, `jet_writeBit_*.v`, `jet_write8_*.v`,
  `jet_write_wide_layout*.v`, `jet_crossing_*.v`, `jet_carry_*_layout.v`.
* Specifications and arithmetic bridges: `jet_spec.v`, `jet_wide_spec.v`,
  `jet_increment8_spec.v`, `jet_add8_word.v`, `jet_increment_wide_word.v`,
  `jet_increment{32,64}_wide_word.v`, `jet_add{16,32,64}_wide_word.v`.
* Complete jet calls: `jet_one8_layout*.v`, `jet_one_wide_layout*.v`,
  `jet_increment8_*.v`, `jet_add8_*.v`, `jet_increment{16,32,64}_layout*.v`,
  `jet_add{16,32,64}_layout*.v`, `jet_arith8_layout_exec.v`.
* Representation, context and execution: `jet_encoding.v`, `jet_bitmachine_rep.v`,
  `jet_context.v`, `jet_canonical.v`, `jet_layout_witness.v`,
  `jet_clight_determinism.v`, `jet_guarantees.v`.
* `check_jet_assumptions.v`: regression print of the assumptions of intermediate
  theorems (informational; the gate is `../audit-jet-assumptions.sh`). It is part
  of `_CoqProject.jets` only.

The increment value bridge for 8 bits exhausts the 256 inputs by kernel-checked
`vm_compute`; it enumerates specification inputs, not C executions.
