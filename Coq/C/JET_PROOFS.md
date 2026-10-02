# C jet implementation-to-Simplicity proofs

Coq proofs that the generated CompCert Clight of 123 jets of the C library
(`C/jets.c`, `C/frame.c`) computes what the corresponding Simplicity expression
computes, and that a call can replace the Bit Machine translation of that
expression in a local, explicitly described context.

| Jet | Simplicity specification |
| --- | --- |
| `low_1/8/16/32/64` | `Word.zero` (the `Prog.zero wordN` specifications of CoreJets) |
| `high_1/8/16/32/64` | `Word.fill Bit.true` (the `Prog.high wordN` specifications of CoreJets) |
| `complement_1/8/16/32/64` | `complement_spec`, the exact recursive `Prog.complement wordN` program |
| `and/or/xor_1/8/16/32/64` | `binary_word_spec`, the exact `Prog.bitwise_bin` recursion with the canonical bit operations |
| `maj/xor_xor/ch_1/8/16/32/64` | `ternary_word_spec`, the existing `Word.bitwiseTri` recursion with `Bit.maj` / `Bit.xor3` / `Bit.ch` |
| `some_1/8/16/32/64`, `all_8/16/32/64` | `predicate_spec`, the exact recursive `Prog.some` / `Prog.all` programs |
| `eq_1/8/16/32/64` | `equality_spec`, the exact Unit/Sum/Prod recursion of `Programs.Generic.eq` |
| `one_8`, `one_16`, `one_32`, `one_64` | `true >>> left_pad_low word1 wordN` |
| `increment_8`, `_16`, `_32`, `_64` | `true &&& iden >>> full_increment wordN` (`increment_word_spec`) |
| `full_increment_8/16/32/64` | `full_increment_word_spec`, the canonical carry-input `Programs.Arith.full_increment wordN` |
| `add_8`, `_16`, `_32`, `_64` | `Word.adder` (`false &&& iden >>> full_add wordN`) |
| `full_add_8/16/32/64` | `Word.fullAdder`, the canonical carry-input `Programs.Arith.full_add wordN` |
| `subtract_8/16/32/64` | `subtract_word_spec`, the canonical `Programs.Arith.subtract wordN` composition |
| `negate_8/16/32/64` | `negate_word_spec`, canonical zero minus the input word |
| `decrement_8/16/32/64` | `decrement_word_spec`, the canonical true-borrow `full_decrement wordN` composition |
| `full_decrement_8/16/32/64` | `full_decrement_word_spec`, the canonical borrow-input zero-subtrahend composition |
| `full_subtract_8/16/32/64` | `full_subtract_word_spec`, the canonical complemented-input full-adder composition |
| `lt/le_8/16/32/64` | `lt_word_spec` / `le_word_spec`, the canonical subtract-borrow and negated swapped-lt compositions |
| `is_zero/is_one_8/16/32/64` | `is_zero_word_spec` / `is_one_word_spec`, canonical negated-some and decrement-payload-zero compositions |
| `min/max_8/16/32/64` | `minmax_word_spec`, canonical le-and-input followed by conditional projections |

Build and reproduction instructions are in [../JET_BUILD.md](../JET_BUILD.md).
The every-jet goal includes the remaining core, Bitcoin and Elements jets;
this document claims completed proofs only for the list above. It makes no
whole-evaluator or machine-code correctness claim. The full inventory and
continuation plan are in [JET_ROADMAP.md](JET_ROADMAP.md).

## What is proved

The results form four layers. Each names the module and theorem; the exact
statements are in the sources.

### 1. Generated Clight against Simplicity (value theorems)

`eval_<jet>_layout_matches_spec` in `jet_one8_layout.v`,
`jet_one_wide_layout.v` (`one_16/32/64`, selected by `W16/W32/W64`),
`jet_increment8_layout.v`, `jet_add8_layout.v`, `jet_increment{16,32,64}_layout.v`
and `jet_add{16,32,64}_layout.v`.

For the ten constants, `jet_constant_layout.v:eval_constant_layout_matches_spec`
is already in canonical-encoding form. `constant_size` selects 1/8/16/32/64
bits, and the boolean selects low/high. It composes the real generated bodies
with the existing total bit, byte and wide writers, sharing one proof of the
complete frame allocation/copy/free lifecycle. `jet_constant.v` isolates
the specification, C literal/cast adapters (including unsigned `UINT32_MAX`
and `UINT64_MAX`), and closed representation bridges.

For complement, `jet_complement{1,8}_layout.v` and
`jet_complement_wide_layout.v` export complete calls already observed through
canonical encodings. `jet_complement_spec.v` defines the exact Haskell program's
recursion and proves a symbolic, width-generic bridge from CompCert integer
negation to that program. No enumeration of larger words is needed.
`jet_readBit_layout.v` proves the actual `peekBit` and `readBit` functions at
arbitrary valid cursors; it exposes the exact returned bit and derives the
cursor store from initial write permission. These helpers do not themselves
count as additional public jets.

For binary and/or/xor, `jet_binary{1,8}_layout.v` and
`jet_binary_wide_layout.v` export complete calls with canonical output
encodings. `jet_binary_spec.v` mirrors `Programs.Word.bitwise_bin` and its
canonical bit operators, proving shared symbolic bridges for both CompCert
integer carriers. The execution adapters distinguish the byte's integer
promotions/truncation, the uniform wide operations, and the one-bit
conditional branches. Both input operands are read before any output write,
including in the short-circuiting one-bit bodies. The bit-reader and
`frame_input_bit_at_preserved` lemmas are reused at arbitrary cursors.

For ternary maj/xor_xor/ch, `jet_ternary{1,8}_layout.v` and
`jet_ternary_wide_layout.v` export fifteen complete calls at 1/8/16/32/64 bits.
`jet_ternary_spec.v` reuses `Word.bitwiseTri`, whose
routing is exactly the canonical Haskell `bitwise_tri` recursion, and its
existing symbolic bit-correctness theorem. New bridges cover both CompCert
carriers without enumerating words. The Clight expression adapter preserves
the generated multiply-by-one inside `ch`'s negation. The layout proof derives
all three readers and the writer before freeing the copied source frame.
The byte adapter accounts for the signed intermediate operations of maj and
xor_xor, ch's mixed signed/unsigned operations, and the final byte cast.
The one-bit adapter executes maj's nested generated conditionals, ch's branch,
and xor_xor's expression. Its finite Boolean cases do not unfold symbolic
memory or enumerate larger words.

For some/all, `jet_predicate_spec.v` mirrors the canonical programs: identity
at one bit, then `Bit.or` / `Bit.and` of the recursive halves. A single symbolic
induction connects these programs to integer comparisons, retaining exact
reader values rather than equality only after lossy decoding. The wide, byte
and one-bit adapters in `jet_predicate*_exec.v` and `jet_predicate*_layout.v`
prove nine complete calls. The byte and wide expressions handle their actual
comparison promotions, including unsigned UINT32_MAX in all_32. These jets
consume the selected input width and write one bit. There is no public all_1
declaration in the inventory; the generic specification's base is shared.

For equality, `jet_equality_spec.v` mirrors `Programs.Generic.eq`, including
the swapped sum routing and product conditional. Its closed symbolic bridge
uses injectivity of the word's exact integer representation. The wide execution
and layout adapters compose two real readers, the unsigned comparison, the
bit writer and local cleanup; they export three complete eq_16/32/64 calls.
The byte adapter accounts for integer promotions and the actual Boolean
argument conversion. The bit adapter reuses two actual readBit calls and
their Boolean casts, without adding fictitious branches or temporaries.
Both export the same canonical, context and call-boundary results.
The specification bridge alone is not counted as jet coverage.

For carry-input increment, `jet_full_increment8_word.v` reuses the existing
canonical full-increment program and byte-adder representation, carry and
modulo lemmas. It supplies a width-generic numeric lemma and a symbolic byte
bridge. `jet_full_increment8_exec.v` executes the actual Boolean/uchar reads,
promotions, comparison, multiply-by-one, casts and both writes. The layout
module derives these calls and local cleanup from initial nine-bit input and
output contracts, with arbitrary valid cursors and unrelated bits. Its public
results include both input carry values, canonical output encoding, represented
context substitution and deterministic call-boundary guarantees.

For carry-input byte addition, `jet_full_add8_word.v` reuses the byte-adder
representation lemmas and the existing canonical `Word.fullAdder` program,
whose recursion matches `Programs.Arith.full_add`. Its symbolic bridge proves
the short-circuit carry and truncated payload without enumerating word inputs.
`jet_full_add8_exec.v` executes the generated conditional assigning `_t'4`,
three real reads, both output writes, return and local cleanup. The layout
module derives these from initial 17-bit input and nine-bit output contracts,
including arbitrary valid cursors, crossings and unrelated output bits.

For borrow-input decrement, `jet_full_decrement_word.v` reuses subtraction's
signed borrow/payload balance and carrier-modulo reduction, with the canonical
`full_decrement_word_spec` composition already defined in `jet_subtract_spec.v`.
Its byte and width-shared adapters follow the checked full-increment frame
lifecycle, but execute the actual unsigned comparison `1U*x < 1U*z` and
subtraction `1U*x-z`. The wide comparison promotes its uint borrow operand to
ulong. Both input borrow values are covered; the initial-only contracts derive
both readers, both writers and cleanup, with arbitrary valid cursors, crossings,
unrelated output bits, canonical encodings and contextual/call-boundary results.

`jet_full_add_wide_word.v` extends this bridge to 16/32/64 bits. It reuses the
existing add overflow lemmas and carry-input increment threshold. The first
carry branch protects the second comparison from the wrapping 64-bit sum;
the payload proof retains modular arithmetic rather than assuming an unbounded
machine sum. `jet_full_add_wide_exec.v` executes both actual conditional branches
and reuses the increment's mixed uint/ulong subtraction adapter. The shared
layout proof derives all three reads, both writes and local cleanup from
initial contracts consuming `1 + 2 * width` input bits and writing `1 + width`
output bits, with the same cursor, encoding and memory-framing guarantees.

`jet_full_increment_wide_word.v` extends this bridge to 16/32/64 bits by
reusing the verified increment bridges for carry one and proving the canonical
carry-zero identity. `jet_full_increment_wide_exec.v` retains the actual
uint subtraction in the 16/32-bit carry expressions before promotion to ulong;
64-bit arithmetic remains in ulong, including wraparound. The shared layout
module derives the bit reader, exact wide reader, both writers and local cleanup
from initial-only contracts, and exports three named canonical local specs,
context substitution and call-boundary guarantees.

For subtraction, `jet_subtract_spec.v` mirrors the actual canonical
`Programs.Arith.full_subtract` composition: complement the second word, invert
the input borrow, run `Word.fullAdder`, then invert the output carry.
`subtract_word_spec` supplies its constant-false input borrow. A signed
borrow/payload balance and word-modulus lemmas connect the actual C values to
this program, rather than replacing it with an independently chosen numeric
specification. `jet_subtract_word.v` handles both carriers symbolically,
including 64-bit wraparound and the byte's signed, promoted comparison.
`jet_subtract{8,_wide}_exec.v` and `jet_subtract{8,_wide}_layout.v` derive two
actual reads, the borrow-bit and payload writes, return and local cleanup from
initial contracts. They export four named canonical local specs, context
substitution and call-boundary guarantees with arbitrary valid cursors,
crossings and unrelated output contents.

`jet_full_subtract_word.v` extends the bridge to both input borrow values,
including the valid endpoint where the mathematical difference is minus the
word modulus. Its carrier-modulo difference lemma handles both subtractions
without assuming their machine intermediates are unbounded integers.
`jet_full_subtract{8,_wide}_exec.v` executes the actual conditional assigning
`_t'4`: first test `1U*x < 1U*y`, otherwise test `1U*x-y < 1U*z`.
The false first test establishes non-wrapping intermediate subtraction for
the second comparison. The byte comparisons are unsigned, unlike plain byte
subtraction; the wide second comparison retains uint-to-ulong promotion.
The shared layout adapters derive three reads, both writes and local cleanup
from initial-only contracts, exporting four canonical local specs plus
context and call-boundary guarantees.

`jet_order_spec.v` mirrors canonical `Programs.Arith.lt` (project subtraction's
borrow) and `le` (negate lt on swapped inputs). A shared balance-sign lemma
reuses the checked subtraction program to connect these compositions to the
actual comparisons. The byte and wide execution/layout adapters share the
checked equality two-reader lifecycle over both operations, preserve signed
byte promotion versus unsigned wide comparison, and derive entry, local-copy,
read, bit-write, return and free from initial contracts. They export eight
named canonical local specs with context and deterministic call guarantees;
the numeric comparison helpers alone do not count as jet coverage.

`jet_test_value_spec.v` mirrors canonical `is_zero` as negated `some`, and
`is_one` as decrement followed by a zero test on its payload. Its symbolic
bridge reuses the checked some recursion and decrement's signed borrow balance,
including zero input wrapping to the maximum payload. Shared byte and wide
execution/layout modules follow the actual comparison-to-zero/one bodies,
derive the single reader and bit writer, and discharge return/local cleanup.
All eight named local specs support arbitrary valid cursors, crossings and
unrelated output bits, with context and deterministic call guarantees.

`jet_minmax_spec.v` mirrors the literal canonical `le &&& iden >>> cond`
compositions, and proves that the C strict-comparison selection has the same
word result, including equal inputs. Shared byte/wide execution adapters
execute the actual conditional assigning `_t'3`, preserving the byte tint
intermediate and uchar writer cast. The layout modules reuse the two-reader
word-writer lifecycle and exact input-value decoding, deriving all reads,
writes, entry, return and local cleanup from initial-only contracts. Eight
named local specs have contextual and deterministic call guarantees.

`jet_borrow_unary_word.v` reuses that signed balance and carrier-modulo bridge
for canonical negation and decrement. It retains the generated nonzero/less-
than-one borrow tests, the byte's promoted comparisons and truncation, and the
wide carrier's wrapping arithmetic. `jet_borrow_unary{8,_wide}_exec.v` and
`jet_borrow_unary{8,_wide}_layout.v` share each carrier's actual body and
initial-only memory proof across both operations, while exporting eight named
canonical local specs. A single actual word read precedes both output writes;
all cursor stores and local allocation/copy/free are discharged, with context
substitution and deterministic call-boundary guarantees.

For the actual generated function body (`f_simplicity_<jet>`), a complete
`ClightBigstep.Clight2.eval_funcall` (parameters as temporaries,
`function_entry2`) exists that returns `true`, has an empty trace, and leaves
memory `mf` such that

* the output cells hold the result of the canonical specification evaluated with
  `Alg.CoreFunSem` (`byte_output_at`, `wide_output_at`, `carry_byte_output_at`,
  `carry_wide_output_at`, or directly `frame_output_cells_at` for constants);
* the final output cursor is the initial cursor minus the output size
  (`frame_fields_at mf ...`);
* the already-written prefix of the topmost touched word is preserved
  (`write_prefix_at`), and every load from a block valid in the initial memory, outside the destination frame item's cursor
  field and the modified word range is unchanged, including other locations of the
  same blocks.

Preconditions concern the **initial** memory only: the input frame item is a
16-byte, 8-aligned region with non-wrapping fields (`frame_base_valid`,
`frame_fields_at`), the represented input bits are readable at their word
locations for an arbitrary non-wrapping cursor (`byte_input_at`,
`frame_input_word_at`, with `read_cursor <= Int64.max_unsigned - N` for `N` input
bits), and the output frame is writable with enough remaining cells
(`write_frame_at`: 8 for `one_8`, 9 for 8-bit increment/add, `wide_bits + 1` for
wide increment/add, and the selected width for constants, complement, binary
and ternary jets). Binary jets consume two
such input words; ternary jets consume three. The some/all predicates require
one writable output cell and consume one input word. Reads and writes may
cross 64-bit word boundaries; other input bits and the initial output word
contents are arbitrary. Every helper call,
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
  `frame_input_word_triple_encode` (three operands),
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

`jet_canonical.v` restates layer 1 for the original twelve jets as
`jet_local_spec f A B spec` (inputs and outputs are `Translate.encode` cells;
`*_local_spec`). The value
theorems are used unchanged.
The constant proofs export `constant_local_spec` and ten named
`low{1,8,16,32,64}_local_spec` / `high{1,8,16,32,64}_local_spec` corollaries.
Complement exports five named `complement{1,8,16,32,64}_local_spec` theorems,
plus context and deterministic execution guarantees (shared over 16/32/64).
Binary exports fifteen named `{and,or,xor}{1,8,16,32,64}_local_spec` theorems,
with `binary1`, `binary8` and `wide_binary` context and guarantee results
parameterized by the operation (and wide size where applicable).
Ternary exports nine named `{maj,xor_xor,ch}{16,32,64}_local_spec` theorems,
with shared `wide_ternary_context` and local/contextual guarantees.
Its byte and bit adapters export the other six named ternary local specs.
Predicates and equality likewise export their nine and five named local specs.
Carry-input arithmetic exports four named `full_increment{8,16,32,64}_local_spec`
and four `full_add{8,16,32,64}_local_spec` results, with byte and width-shared
context and call-boundary guarantees.
Borrow-input decrement likewise exports four named
`full_decrement{8,16,32,64}_local_spec` results and the same guarantee layers.
Borrow-input subtraction exports four named
`full_subtract{8,16,32,64}_local_spec` results and the same guarantee layers.
Ordering exports eight named `{lt,le}{8,16,32,64}_local_spec` results, with
byte and width-shared context and call-boundary guarantees over the operation.

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
`jet_constant_layout.v:constant_context` instantiates the same result for
all ten constants, using `constant_spec_parametric`.

The premises are satisfiable in evaluator shape: `jet_layout_witness.v`
constructs, for arbitrary `a`, `z`, `w`, a two-allocation layout with an inactive
read frame holding `z`, the `increment_64` input `a`, a 65-cell output frame and
an inactive write frame holding `w`, proves `bm_rep`, `bm_separated` and the
permissions together with `gap_buffer_layout`, and derives (`increment64_layout_witness_context`) that the call
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
with layers 1 and 3: `jet_local_spec_guarantees` retains the output, cursor,
written prefix and preservation of loads from initially valid blocks;
`jet_context_guarantees` retains the final represented state and abstract
translation. All twelve jets export both `<jet>_guarantees` (the complete local
contract) and `<jet>_context_guarantees` (the represented-context contract).
The constants export the width/low-high-parameterized `constant_guarantees`
and `constant_context_guarantees`, derived through these same generic results.

## Coverage

| Jet | Value theorem | Canonical / context | Call-boundary |
| --- | --- | --- | --- |
| `low/high_1/8/16/32/64` | `eval_constant_layout_matches_spec` | ten named local specs; `constant_context` | `constant_guarantees`, `constant_context_guarantees` |
| `complement_1/8/16/32/64` | bit/byte/wide layout theorems | five named local specs; bit/byte/wide contexts | bit/byte/wide local and contextual guarantees |
| `and/or/xor_1/8/16/32/64` | `eval_binary1_layout_matches_spec`, `eval_binary8_layout_matches_spec`, `eval_wide_binary_layout_matches_spec` | fifteen named local specs; bit/byte/wide contexts | bit/byte/wide local and contextual guarantees |
| `maj/xor_xor/ch_16/32/64` | `eval_wide_ternary_layout_matches_spec` | nine named local specs; `wide_ternary_context` | `wide_ternary_guarantees`, `wide_ternary_context_guarantees` |
| `maj/xor_xor/ch_1/8` | bit/byte ternary layout theorems | six named local specs; bit/byte contexts | bit/byte local and contextual guarantees |
| `some_1/8/16/32/64`, `all_8/16/32/64` | bit/byte/wide predicate layout theorems | nine named local specs; bit/byte/wide contexts | bit/byte/wide local and contextual guarantees |
| `eq_1/8/16/32/64` | bit/byte/wide equality layout theorems | five named local specs; bit/byte/wide contexts | bit/byte/wide local and contextual guarantees |
| `one_8` | `eval_one8_layout_matches_spec` | `one8_local_spec`, `one8_context` | `one8_guarantees` |
| `one_16/32/64` | `eval_one_wide_layout_matches_spec W16/W32/W64` | `one{16,32,64}_local_spec`, `_context` | `one{16,32,64}_guarantees` |
| `increment_8` | `eval_increment8_layout_matches_spec` | `increment8_local_spec`, `increment8_context` | `increment8_guarantees` |
| `add_8` | `eval_add8_layout_matches_spec` | `add8_local_spec`, `add8_context` | `add8_guarantees` |
| `increment_16/32/64` | `eval_increment{16,32,64}_layout_matches_spec` | `increment{16,32,64}_local_spec`, `_context` | `increment{16,32,64}_guarantees` |
| `add_16/32/64` | `eval_add{16,32,64}_layout_matches_spec` | `add{16,32,64}_local_spec`, `_context` | `add{16,32,64}_guarantees` |
| `full_increment_8/16/32/64` | byte/wide full-increment layout theorems | four named local specs; byte/wide contexts | byte/wide local and contextual guarantees |
| `full_add_8/16/32/64` | byte/wide full-add layout theorems | four named local specs; byte/wide contexts | byte/wide local and contextual guarantees |
| `full_decrement_8/16/32/64` | byte/wide full-decrement layout theorems | four named local specs; byte/wide contexts | byte/wide local and contextual guarantees |
| `full_subtract_8/16/32/64` | byte/wide full-subtract layout theorems | four named local specs; byte/wide contexts | byte/wide local and contextual guarantees |
| `lt/le_8/16/32/64` | byte/wide ordering layout theorems | eight named local specs; byte/wide contexts | byte/wide local and contextual guarantees |
| `is_zero/is_one_8/16/32/64` | byte/wide test-value layout theorems | eight named local specs; byte/wide contexts | byte/wide local and contextual guarantees |
| `min/max_8/16/32/64` | byte/wide minmax layout theorems | eight named local specs; byte/wide contexts | byte/wide local and contextual guarantees |

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
assuming it succeeds). The caller's environment argument is an arbitrary CompCert `val`, including
the evaluator's transaction-environment pointer; none of these jets reads it. Frames are 16-byte `frameItem`s: the edge pointer at offset 0,
the offset at offset 8. Other ABIs, fully debug-enabled execution, and jets wider
than 64 bits are not covered.

## Assumptions

Public types and their contract definitions are frozen in `jet_contracts.expected`
and enforced by `../audit-jet-contracts.sh`; intentional contract changes require
review of that diff. Public theorems are checked with `coqchk` and their axiom sets are recorded in
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
  therefore by `jet_clight_determinism.v`, `jet_guarantees.v` and the constant
  call-boundary guarantees.
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
regeneration is configured in the `jets-ast` CI job; an executed Linux run is
required before claiming that host has been verified.

## Structure copies and VST

Clightgen's `-normalize -fstruct-passing` gives each jet a by-value `frameItem`
parameter `_src` and a local variable of the same name; the first statement is
`Sassign (Evar _src) (Etempvar _src)`, a struct copy (`assign_loc_copy`) into a
freshly allocated local, whose address is then passed to the readers. The proofs
therefore carry explicit preconditions for this copy (a readable, 8-aligned,
16-byte source, `Mem.loadbytes`/`frame_base_valid`, and the non-overlap that the
fresh block provides) and use `jet_frame_copy.v`, `jet_frame_copy_layout.v` to
show the copied fields equal the source's.

The proofs are direct Clight big-step proofs. The pinned VST 2.14 manual
(`doc/VC.tex`, supported C subset) explicitly excludes struct-copy assignments,
struct parameters and struct returns. These entry functions have a struct
parameter and a genuine struct-copy assignment, so ordinary Verifiable C
`semax_body` proofs cannot verify the entrypoints as written. Pointer-based
helpers can use VST. Sharing `function_entry2` with `veric/Clight_core.v` does
not remove the supported-language restriction.

Mainline's `Coq/C/secp256k1/` uses VST Floyd specifications and `semax_body`
proofs of internal helpers; it does not provide an entrypoint template for
these by-value jets. Reusing that approach for the entrypoints would require
changing the C interface or extending Verifiable C, defining frame predicates
and connecting them to `bm_rep`. Moreover, `semax` proves partial correctness
and safety; the existence and termination guarantees exported here would still
need an additional adequacy/termination argument. The direct Clight proofs are
retained for these reasons. VST remains a dependency for the imported `sha`
library.

## Remaining boundaries

* Linking: all calls use `ge0 = Clight.globalenv prog` for the generated
  jets/frame translation unit. Applying them in the separately compiled
  evaluator also needs an environment/linking preservation argument. An
  arbitrary environment pointer alone does not establish that argument.
* Whole-evaluator correctness: nothing proves that every evaluator execution
  establishes `bm_rep`/`bm_separated` before a jet call, or that replacing
  translated code by jet calls is correct for whole programs.
* Machine code: correctness is for Clight, not for the code a C compiler emits.
* The C-to-AST step is checked by regeneration only.
* Other configurations: other targets, `PRODUCTION` off, wider jets.
* `coqJets` and the shell verification pipeline were executed on macOS/arm64
  after review remediation (see `../JET_BUILD.md`). The configured GitHub
  Actions jobs, Linux AST regeneration and the full six-hour `coq` build have
  not been executed for these changes.

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

Module map: `Coq/_CoqProject.jets` contains the public dependency closure.
Earlier modules still needed by those proofs remain in it. Nineteen superseded
position/crossing results and the informational `check_jet_assumptions.v` are
retained in `Coq/_CoqProject.jets-regression`, built explicitly with
`build-jets.sh --regression`; they are not dependencies of the public results.

* Generated code and execution: `jets.v`, `jet_exec.v`, `jet_one8.v`,
  `jet_read8.v`, `jet_write8.v`, `jet_writeBit.v`, `jet_increment8.v`,
  `jet_add8.v`, `jet_wide.v`.
* Frame and layout contracts: `jet_frame_spec.v`, `jet_frame_layout.v`,
  `jet_frame_access.v`, `jet_frame_arith.v`, `jet_frame_constants.v`,
  `jet_frame_copy.v`, `jet_frame_copy_layout.v`, `jet_input_layout.v`,
  `jet_input_position.v`, `jet_output_layout.v`, `jet_output_layout_step.v`,
  `jet_output9.v`, `jet_output_slice.v`, `jet_two_word_input.v`.
* Bit algebra: `jet_word_bits.v`, `jet_word_decode.v`, `jet_word_position.v`,
  `jet_word_slice.v`, `jet_toZ.v` (shared interpretation injectivity),
  `jet_word_repr.v` (width-generic range and decoding facts,
  shared by the 16-, 32- and 64-bit readers and `jet_encoding.v`),
  `jet_LSBclear_width.v`, `jet_LSBkeep_width.v`.
  `jet_complement_spec.v` and `jet_binary_spec.v` add shared symbolic
  bridges to the exact canonical bitwise programs.
  `jet_ternary_spec.v` reuses the existing ternary recursion and bit theorem.
* Readers: `jet_reader_total.v` (shared cursor-store and memory-preservation
  proof), `jet_read8*.v`, `jet_read{16,32,64}_layout_exec.v`,
  `jet_read{16,32,64}_layout_total.v`, `jet_read{16,32,64}_input_word*.v`.
* Writers: `jet_write*_layout*.v`, `jet_writeBit_*.v`, `jet_write8_*.v`,
  `jet_write_wide_layout*.v`, `jet_crossing_*.v`, `jet_carry_*_layout.v`.
* Specifications and arithmetic bridges: `jet_spec.v`, `jet_increment_spec.v`
  (shared canonical increment program), `jet_wide_spec.v`,
  `jet_increment8_spec.v`, `jet_add8_word.v`, `jet_increment_wide_word.v`,
  `jet_increment{32,64}_wide_word.v`, `jet_add{16,32,64}_wide_word.v`.
  Carry-input bridges use `jet_full_increment8_word.v`,
  `jet_full_increment_wide_word.v`, `jet_full_add8_word.v` and
  `jet_full_add_wide_word.v`.
* Complete jet calls: `jet_one8_layout*.v`, `jet_one_wide_layout*.v`,
  `jet_increment8_*.v`, `jet_add8_*.v`, `jet_increment{16,32,64}_layout*.v`,
  `jet_add{16,32,64}_layout*.v`, `jet_arith8_layout_exec.v`.
  Constants, complement and binary operations use `jet_constant*.v`,
  `jet_complement{1,8}_*.v`, `jet_complement_wide_*.v`,
  `jet_binary{1,8}_*.v` and `jet_binary_wide_*.v`.
  `jet_ternary_wide_{exec,layout}.v` supplies the three-reader wide calls.
  Predicate, equality and carry-input arithmetic calls use
  `jet_predicate{1,8,_wide}_{exec,layout}.v`,
  `jet_equality{1,8,_wide}_{exec,layout}.v`,
  `jet_full_increment{8,_wide}_{exec,layout}.v` and
  `jet_full_add{8,_wide}_{exec,layout}.v`.
* Representation, context and execution: `jet_encoding.v`, `jet_bitmachine_rep.v`,
  `jet_context.v`, `jet_canonical.v`, `jet_layout_witness.v`,
  `jet_clight_determinism.v`, `jet_guarantees.v`.
* `check_jet_assumptions.v`: regression print of the assumptions of intermediate
  theorems (informational; the gate is `../audit-jet-assumptions.sh`). It is part
  of `_CoqProject.jets` only.

The increment value bridge for 8 bits exhausts the 256 inputs by kernel-checked
`vm_compute`; it enumerates specification inputs, not C executions.
