# Every-jet implementation-to-specification goal

Prove every individual public C jet equivalent to its Simplicity program,
including application primitives. Mathematical properties of the specifications
and helper correctness alone do not count as jet coverage. No proof escapes,
new axioms or pushes. Reuse completed proofs and proceed easiest to hardest.

## Scope and status

The public surface currently has 533 distinct declarations: 370 in `C/jets.h`,
60 in `C/bitcoin/bitcoinJets.h`, 103 in `C/elements/elementsJets.h`.
`../jet-coverage.py` derives this inventory from those headers and both
`primitiveJetNode.inc` registration catalogs, rather than maintaining a fixed
list of missing jets. `jet_coverage.tsv` maps completed functions to audited,
named canonical implementation-to-specification theorems. It is bookkeeping,
not an independent proof checker; `../check-jets.sh` builds and checks proofs.

There are 206 registered core proof entries: verify, parse_lock, parse_sequence,
sha_256_iv and sha_256_ctx_8_init; left_pad_low_1/right_pad_low_1/left_extend_1 at
8/16/32/64 bits; left_extend_8/right_extend_8 at 16/32/64 bits;
left/right_extend_16 at 32/64 bits and left/right_extend_32_64;
left/right_rotate, left/right_shift and left/right_shift_with at 8/16/32/64 bits;
one/increment/add/full_increment/full_add/subtract/negate/decrement/full_decrement/full_subtract/lt/le/is_zero/is_one/min/max/median/divide/modulo/divides/div_mod at 8/16/32/64 bits,
low/high/complement/and/or/xor/maj/xor_xor/ch/some at 1/8/16/32/64 bits,
all at 8/16/32/64 bits, eq at 1/8/16/32/64/256 bits, multiply/full_multiply at 8/16/32/64 bits, and div_mod_128_64.
The accepted baseline leaves 326 declarations without audited coverage,
including 59 Bitcoin jets and all Elements jets. The latest completed
integration covers 207 public entries,
including sha_256_ctx_8_init, DivMod128_64, multiply64 and fullMultiply64
(410 result modules / 1848 results, 776 closed). Audit `94007`'s build/kernel/assumption/
contract gates were observed passing; recovery `33472` completed its unobserved
negative fixtures and exact pinned AST regeneration with terminal exit 0. The
prescribed snapshot filters reproduce accepted `a77fcf0` byte-for-byte and the
15 inherited kernel axioms are unchanged. Expanded reader-support audit `51817`
subsequently passed all gates, negative fixtures and exact pinned AST regeneration
with terminal exit 0. Its prescribed filters reproduce `b941abc` byte-for-byte;
the inherited kernel axioms remain unchanged. The ten reader-support modules
add no public coverage. Their snapshots are accepted. The complete mixed-reader
and byte-writer consumers subsequently passed expanded audit `13723`, including
all gates, negative fixtures and exact AST regeneration with terminal exit 0.
Prescribed filters reproduce `0ddec7c` byte-for-byte; inherited axioms are
unchanged. These consumer snapshots are accepted without adding public coverage.
Expanded mixed-writer audit `30018` also passed all gates, negative fixtures
and exact AST regeneration with terminal exit 0. Its prescribed filters
reproduce `9cc50d6` byte-for-byte; inherited kernel axioms are unchanged.
The seven mixed-writer support modules are accepted, with no public coverage added.
General context-writer / readonly-provenance audit `58720` subsequently passed
every gate, negative fixture and exact AST regeneration with terminal exit 0.
Both prescribed filters reproduce `dd2b9d7` byte-for-byte, with unchanged
inherited kernel axioms. Its four additional modules are accepted as helper
support, not additional public coverage.
Complete initial-memory context-reader audit `69867` subsequently passed all
gates, negative fixtures and exact pinned AST regeneration with terminal exit 0.
The prescribed filters reproduce `5fffb98` byte-for-byte and inherited kernel
axioms are unchanged. Its seven helper modules are accepted without adding public
coverage. The literal count-assertion and reader-return bridge are independently
checked but not yet included in these integrated totals.
Count/assertion bridge audit `46115` has now passed every gate, negative fixture
and exact pinned AST regeneration with terminal exit 0. Its snapshot filters
reproduce `8f2f694` byte-for-byte, with unchanged inherited kernel axioms.
Those three support modules are accepted in the totals above; canonical writer,
roundtrip and Bitcoin groundwork remain independently checked but unregistered.
Ge-parametric helper integration `70050` subsequently passed every gate,
negative fixture and exact core AST regeneration with terminal exit 0. It
checks 398 result modules / 1808 results, 754 closed; both prescribed snapshot
filters reproduce `c8cbaeb` byte-for-byte and inherited kernel axioms are
unchanged. Public coverage remains 206 entries.
The Bitcoin version groundwork now includes a complete independently checked
canonical local-contract theorem in `jet_bitcoin_version_local.v`: actual
Bitcoin-program execution, initial-memory environment projection, allocation /
source copy / writer / cleanup, and the encoded result of literal primitive
Version. It is not yet included in the 206 audited coverage entries. Next
register its concrete artifact and support modules, extend application-contract
coverage validation with negative tests, and check exact Bitcoin AST regeneration
in the integrated gate. Do not count helper modules as additional jets.
Version integration `9008` passed build/kernel/assumption checks but terminated
on a contract-manifest library-path error. The metadata path is fixed and
recovery `9432` passed kernel/assumption/contract/negative/dual-AST gates with
terminal exit 0, reusing the completed unchanged-source build. Both actual
snapshot filters reproduce `9c09d18` byte-for-byte; inherited kernel axioms are
unchanged. The version jet is accepted as the first Bitcoin coverage entry.
The shared getter32 execution/initial-memory contracts and the actual lock-time
and CurrentIndex canonical local theorems are independently kernel-checked,
but remain unregistered. Next integrate both with their support chain in a
separate snapshot/coverage audit.

Canonical-spec caution: NumInputs/NumOutputs are **not** direct primitives in
the current Haskell jet catalog. `Programs.Transaction.lib` defines them as
`firstFail word32 (primitive InputValue/OutputValue)`. The older Coq Bitcoin
primitive module still has NumInputs/NumOutputs constructors, but proving the C
getters against those alone would not establish the requested literal-program
equivalence. Port/check the actual firstFail programs and their environment
interpretations before registering count-jet coverage. The C getters do share
the getter32 wrapper, with checked field offsets 448/456, so their execution
proofs can later reuse the same infrastructure.
Coverage is for the pinned
PRODUCTION LP64 Clight configuration, not other ABIs or debug builds.

Two core declarations are not registered in either application catalog:
`simplicity_off_curve_scale` and `simplicity_off_curve_linear_combination_1`.
Keep them visible. Resolve their intended specifications or obsolete status
explicitly; do not quietly exclude them to obtain a complete count.

Commands from the repository root:

```sh
python3 Coq/jet-coverage.py
python3 Coq/jet-coverage.py --csv
python3 Coq/jet-coverage.py --require-complete
opam exec --switch=simplicity -- bash Coq/check-jets.sh --ast
```

The completeness command intentionally fails while any declaration lacks a
proof entry. Passing the normal checks certifies existing proofs, not completion
of the every-jet goal. Nix uses the same gates and supplies the C inventory
through `Simplicity.JetInventory.nix` / `JET_C_REPO`, because its proof source
tree otherwise contains only Coq files.

## Reusable proof structure and next families

1. **Constants: completed.** `jet_constant.v` isolates actual function
   selectors, canonical programs, literal evaluations/casts and representation
   bridges. `jet_constant_exec.v` composes function entry, the generated body,
   return conversion and freeing locals. `jet_constant_writer.v` unifies the
   existing total bit/byte/wide writers. `jet_constant_layout.v` derives all
   intermediate allocations and stores from initial contracts, exports ten
   canonical local specs, and reuses context and call-boundary guarantees.
   The bridges compute closed constants only; symbolic memory is not unfolded.
2. **Complement and binary and/or/xor: completed.** Five complement calls
   reuse total readers/writers, frame lifecycle, canonical encodings,
   contexts and guarantees. `jet_complement_spec.v` defines the exact canonical
   recursion (base `Bit.not iden`, successor `take rec &&& drop rec`). Its
   symbolic bridge uses `Word.testbitToZLo` / `Word.testbitToZHi` by induction,
   followed by `Int.bits_not` / `Int64.bits_not`, accounting for truncation.
   `Word.bitwiseTri_correct` cannot prove complement: its zero-preservation
   premise is false for negation. `jet_readBit_layout.v` now proves both actual
   bit-reader bodies at arbitrary layouts, including the exact returned bit
   and cursor increment. Reuse it for one-bit variants and carry-input jets.
   Fifteen binary calls use `jet_binary_spec.v`, which mirrors the canonical
   `Programs.Word.bitwise_bin` recursion exactly and proves shared symbolic
   bit bridges for both CompCert carriers. `jet_binary_wide_exec.v` and
   `jet_binary_wide_layout.v` parameterize the operation and W16/W32/W64.
   `jet_binary8_*.v` account for promotions and truncation; `jet_binary1_*.v`
   execute the actual and/or conditional branches and the XOR expression.
   All adapters derive two readers and one writer from initial contracts,
   and export canonical/context/call-boundary results. Both inputs are read
   even in the one-bit and/or bodies. Reuse the shared bit-preservation lemma
   and these sequencing proofs for subsequent readers.
   **Ternary operations completed.** Fifteen maj/xor_xor/ch calls reuse
   Coq Word's existing `bitwiseTri` and `bitwiseTri_correct`: the recursion
   and Bit.maj/xor3/ch bases were checked against the canonical Haskell
   programs. `jet_ternary_spec.v` supplies closed symbolic bridges for both
   CompCert carriers, preserving the actual multiply-by-one in ch.
   `jet_ternary_wide_exec.v` shares the binary reader-call adapter and a new
   long-expression lemma. `jet_ternary_wide_layout.v` derives three reads,
   one write and the complete frame lifecycle, exporting canonical, context
   and call-boundary results. `frame_input_word_triple_encode` bridges the
   nested canonical input product to its three physical word contracts.
   `jet_ternary8_*.v` and `jet_ternary1_*.v` now complete the byte and bit
   variants, retaining separate promotions and branching adapters.
   The byte adapters reuse `binary8_read` / `call_binary8_read` with
   `_t'1`, `_t'2`, `_t'3`. The maj/xor_xor intermediates are `tint`, but ch's
   multiply/negation/second-and/final-or are `tuint`; its first-and is `tint`.
   `eval_int_bin` handles actual signed/unsigned bitwise intermediates.
   `ternary_int_denotes` supplies the symbolic specification bridge, and the
   actual writer's byte cast performs truncation. Input uses
   `frame_input_word_triple_encode` and `byte_slice_at_encode`, with the
   non-wrapping 24-bit consumption bound.
   The one-bit adapters reuse `binary1_read` / `call_binary1_read`,
   `eval_readBit_layout`, `eval_writeBit_layout` and single-bit preservation.
   All three bits are read first, and results are normalized to `bit_int`.
   The bounded structural tactic executes the actual conditional subtrees
   after splitting the three booleans; it computes only closed branch
   conditions, never symbolic memory. Pattern-match on the exposed
   `exec_stmt function_entry2` head, not its `Clight2.exec_stmt` alias after
   constructors have unfolded it. Inspect the first failing leaf rather than
   wrapping a recursive tactic in rollback-producing `try`.
   **Some/all predicates completed.** Nine calls use `jet_predicate_spec.v`,
   which mirrors identity at one bit and recursive `Bit.or` / `Bit.and` of the
   halves. `predicate_spec_numeric` supplies a closed symbolic induction;
   `word_modulus` and bounds on each half allow reasoning about zero and
   maximum values without enumerating words. Keep the modulus symbolic when
   simplifying arithmetic: `cbn -[word_modulus]`, not unrestricted `cbn`.
   `jet_predicate_wide_*.v` and `jet_predicate8_*.v` compose exact reader-value
   bridges with the actual comparisons and the total bit writer.
   all_32 promotes unsigned 32-bit UINT32_MAX to the 64-bit carrier, whereas
   all_64 uses a long literal. `jet_predicate1_*.v` proves some_1's identity
   call and reuses the existing bit-reader call adapter. There is no public
   all_1 declaration; do not invent an extra covered jet.
   **Small-width equality completed.** eq_1/8/16/32/64 reuse two exact readers and
   the total bit writer. `jet_equality_spec.v` supplies the shared canonical
   recursion, its parametricity and a closed symbolic numeric bridge using
   `toZ_injective`. The byte adapter handles promoted comparison; the bit
   adapter uses normalized Boolean carriers. Next: carry-input arithmetic,
   then eq_256 when its additional local-array and loop infrastructure is ready.
   Equality's canonical program is `Programs.Generic.eq`, not bitwise XOR
   or a newly chosen mathematical predicate. Mirror its actual Unit/Sum/Prod
   recursion (including swap and case routing); prove the numeric bridge
   separately and then use the existing two-reader sequencing with a bit
   writer. eq_256 additionally has a local array and loop, so the small-width
   adapter alone will not discharge its function-entry and memory obligations.
3. **Arithmetic families.** Subtraction/decrement and carry-input variants
   should reuse the increment/add machine-value, carry and word-modulo facts.
   Keep width-independent arithmetic separate from generated-body adapters.
   Afterwards tackle shifts/rotates, multiplication, division and larger widths.
   **full_increment_8/16/32/64 completed.** Reuse the existing literal canonical
   `full_increment_word_spec` and its parametricity, not a new numeric spec.
   `jet_full_increment8_word.v` proves its width-generic numeric bridge and
   reuses byte-adder carry/modulo lemmas without enumerating words. The actual
   call proof composes a bit reader, a byte reader, carry-plus-byte output
   and local cleanup. The wide modules reuse the shared wide reader and carry
   writer, and the already checked increment bridges for carry one. A shared
   carry-zero identity avoids duplicating overflow proofs. Preserve the
   generated mixed carrier operations: the 16/32-bit
   carry subtraction occurs in uint before comparison with ulong, whereas
   64-bit subtraction and sum use ulong. Do not assume the 64-bit sum is the
   unbounded sum; reuse its existing wraparound bridge. **full_add_8/16/32/64 completed**
   using a carry-bit read followed by the two existing word reads. Its generated carry
   is a short-circuit conditional assigning `_t'4`, not a single expression.
   Execute that branch explicitly before composing the carry and word writers.
   The byte proof reuses `add8_u_range`, `read8_result_unsigned` and
   `decode_word8_of_int`, connects the actual carry and payload to canonical
   `Word.fullAdder`, and derives all three reads and local cleanup from initial
   17-bit input contracts. The wide extension preserves the mixed uint/ulong
   second comparison and wrapping 64-bit intermediate sum. Its shared first
   carry lemma reuses the existing add bridges; when that carry is false,
   the intermediate sum is exact and the increment threshold applies. The
   payload proof is modular at 64 bits. All three widths share one complete
   layout proof consuming `1 + 2 * width` bits and producing `1 + width` bits.
   **subtract_8/16/32/64 completed.** `jet_subtract_spec.v` mirrors
   canonical `Programs.Arith.full_subtract`: complement the second word,
   invert the input borrow, run full_add, then invert its output carry.
   `subtract_word_spec` fixes its input borrow to false. The shared signed
   borrow/payload balance is injective; a modular representation bridge reuses
   `Word.fullAdder_correct` and complement's numeric identity. Machine carrier
   reduction uses `Znumtheory.Zmod_div_mod`, including wrapping 64-bit
   subtraction. The byte borrow comparison is signed `Int.lt` after integer
   promotion, justified by the operands' byte ranges; wide comparison is
   `Int64.ltu`. All four complete calls reuse two-reader sequencing and the
   total carry-plus-word writers, deriving allocations/stores/free from initial
   contracts and supporting arbitrary valid cursors and crossings.
   **negate_8/16/32/64 and decrement_8/16/32/64 completed.**
   `jet_borrow_unary_word.v` shares the canonical zero/constant-input programs,
   signed balance and carrier-modulo bridges across both operations. The
   byte and wide execution/layout modules each share one-reader sequencing
   and borrow-plus-word writing across negate/decrement, exporting eight
   named local specs with initial-only frame contracts. Preserve the actual
   comparisons (`x != 0` versus `x < 1`), byte promotions and truncation,
   and the generated multiply-by-one inside negation or subtraction.
   **full_decrement_8/16/32/64 completed.** `jet_full_decrement_word.v` reuses
   the canonical composition, signed balance and subtraction modulus lemmas.
   Both borrow inputs and all widths have complete initial-only local specs,
   context substitution and call-boundary guarantees. Its execution/layout
   adapters reuse the full-increment frame lifecycle.
   full_decrement reads a bit followed by a word and tests `1U*x < 1U*z`;
   unlike plain byte decrement, its byte comparison is **unsigned** after the
   generated multiply-by-one. Normalize the returned Boolean exactly and
   retain the wide-versus-uint carrier conversion. Start from
   `jet_full_increment{8,_wide}_layout.v` for its bit-plus-word input and
   two-writer output, and reuse subtraction's modulus reduction for `x-z`.
   Its checked canonical numeric bridge is `full_subtract_word_spec_numeric`
   with second word zero; both borrow values are covered.
   **full_subtract_8/16/32/64 completed.** `jet_full_subtract_word.v` supplies
   the symbolic borrow and two-subtraction modular payload bridge; byte and
   width-shared execution/layout modules reuse full-add's three-reader frame
   lifecycle and derive all intermediate calls and cleanup from initial-only
   contracts. They export four named canonical local specs, contexts and
   call-boundary guarantees. These are complete C proofs, not just helper results.
   full_subtract has a generated short-circuit conditional assigning `_t'4`;
   do not treat it as a single expression. The first test is `1U*x < 1U*y`,
   also unsigned in the byte body, followed only when false by
   `1U*x-y < 1U*z`. That false-branch inequality establishes that `x-y` has
   not wrapped before the second comparison. Its payload retains both
   subtractions and final cast. Start from the checked full-add three-reader
   and conditional sequencing, not the plain subtract body.
   For its representation bridge, allow the endpoint `delta = -word_modulus n`
   (`0 - max_word - true`); `borrow_mod_balance` already covers that inclusive
   lower bound. A strict lower bound would incorrectly discard a valid input.
   **lt/le_8/16/32/64 completed.** `jet_order_spec.v` mirrors the canonical
   compositions and uses the subtraction balance sign for their symbolic
   numeric bridges. Byte and width-shared execution/layout modules reuse
   equality's two-reader lifecycle, parameterized by both operations. All
   eight named local specs derive the complete calls from initial contracts,
   with context substitution and call-boundary guarantees.
   `Programs.Arith.lt` projects the borrow from canonical subtract;
   `le` negates lt on swapped inputs. Reuse the signed balance to connect these
   exact programs to the actual C comparisons; the adapters use two-reader
   sequencing and the total bit writer. Byte comparisons are signed after promotion
   (justify with byte bounds); wide comparisons are unsigned.
   **is_zero/is_one_8/16/32/64 completed.** `jet_test_value_spec.v` mirrors
   canonical `not (some wordN)` and decrement followed by payload is_zero.
   The width-independent numeric bridge reuses the some recursion and the
   checked signed decrement balance; the modulus is at least two, excluding
   a zero payload at zero input after wrapping. Shared byte/wide execution and
   layout modules reuse the one-reader predicate lifecycle, with eight named
   canonical local specs and contextual/call-boundary guarantees.
   **min/max_8/16/32/64 completed.** `jet_minmax_spec.v` mirrors le-and-input
   followed by conditional projections. Its strict-selection bridge accounts
   for equal inputs using word-value injectivity. Shared byte/wide adapters
   execute the `_t'3` conditional assignment before the word writer, preserving
   byte promotions and the final uchar cast. The initial-only layout proofs
   export eight named local specs, contexts and deterministic call guarantees.
   **median_8/16/32/64 completed.** The literal nested min/max composition is
   bridged symbolically to the generated comparison tree. `jet_median_control.v`
   shares the entire branch/cast proof across byte/wide carriers, including the
   two/three `_t'4` assignments per leaf. Carrier adapters discharge all of its
   internal expression premises. Three-reader layout adapters reuse minmax's
   exact input-value decoding and export four named canonical local specs,
   contextual substitutions and deterministic call guarantees.
   **forwardBits cursor helper completed.** `jet_forwardBits_layout.v` executes
   the actual generated function and derives its cursor store and preservation
   from initial frame fields, writable cursor access and a non-wrapping bound.
   It is shared infrastructure, not another public jet equivalence proof.
   **Next: shared copyBits contracts and leftmost/rightmost
   projections**, then shifts/rotates, multiplication and division. Inspection
   of the actual generated bodies shows that these projections call
   `simplicity_copyBits`, not the existing word readers/writers. Rightmost first
   calls `forwardBits` on the local source-frame copy. Prove these actual helpers
   from initial frame contracts, including crossings and permitted memory
   effects, rather than applying an arithmetic reader/writer adapter to a
   different body. Reuse Coq Word's existing `leftmost`/`rightmost` and their
   parametricity: their identity/take/drop vector recursion matches the Haskell
   catalog. All 36 projection declarations, including 2/4-bit outputs, remain
   in scope; copyBits handles these widths without invented public writers.
   Its verified contract should also support padding and full-shift families.
   **Check separation before copying.** `copyBitsHelper` clears destination
   bits before reading the source in its partial-word branch, and its aligned
   branch uses `memcpy`. Unlike read-all-inputs-before-writing arithmetic jets,
   its proof must not assume that arbitrary overlapping buffers are supported.
   The evaluator's represented caller already supplies `bm_separated` ranges.
   Derive a suitable copy contract from those invariants, preserving all valid
   caller layouts and keeping existing stronger arithmetic contracts unchanged.
   **Separated-call interface completed.** `jet_context_separated.v` defines
   an initial-only `jet_separated_local_spec` with the same output and framing
   observations as `jet_local_spec`. Its additional buffer-separation predicate
   is derived formally from `bm_rep` / `bm_separated`, including shared cell
   blocks and arbitrary caller cursors. `jet_context_separated` therefore has
   the same represented-caller premises and replacement conclusion as
   `jet_context`; no stronger contextual premise is added. Existing arithmetic
   results imply the new local interface, but retain their stronger originals.
   This is an interface proof, not a copyBits implementation proof or added
   coverage. Extend the inventory's accepted theorem shapes and negative tests
   explicitly when the first complete projection theorem uses this interface.
   **copyBits wrapper composition completed.** `jet_copyBits_exec.v` executes
   the actual wrapper's zero-count return without memory effects. For nonzero
   counts, its INTERNAL composition theorem executes the helper call and cursor
   update; the store/framing corollary derives the cursor store from the helper's
   resulting fields and permissions. These are not complete copyBits contracts:
   actual `copyBitsHelper` execution and its post-helper cursor facts remain
   premises to discharge from initial frame conditions. Prove its partial-word,
   aligned memcpy and loop branches before adding any projection coverage.
   **First copy-helper return branch completed.**
   `jet_copyBits_helper_exec.v` derives all four generated pointer/shift
   initializations and executes the complete helper call when
   `0 < n <= src_shift < dst_shift` (a partial destination word). Its
   initial-only theorem derives both stores from writable access and the
   intervening source load from word separation; the destination frame fields,
   outside-word loads, permissions and valid blocks are preserved. No
   intermediate execution/store premise remains in that theorem. Other
   partial-word branches, crossings, aligned memcpy and the loop are still
   outstanding, so this adds no projection coverage.
   **Both non-crossing partial-word returns and their wrapper completed.**
   `jet_copyBits_helper_right.v` handles `src_shift >= dst_shift > 0` and
   `n <= dst_shift`. It shares `eval_copy_helper_partial_from_tail` with the
   first branch: intermediate store/execution premises are INTERNAL and are
   discharged by both initial-only branch theorems. `jet_copyBits_short_exec.v`
   combines them for `0 < n <= src_shift` and `n <= dst_shift` and derives the
   actual `simplicity_copyBits` call, its cursor update, resulting word and
   load/permission/block framing. `jet_copyBits_short_word.v` bridges both
   stored values symbolically to copied bits and preserved written bits.
   These results do not cover an initially aligned destination or a crossing.
   **Short-copy frame-cell contract completed.**
   `jet_copyBits_short_cells.v:eval_copyBits_short_layout` takes logical input
   cells and the existing `write_frame_at` predicate. It derives the source
   word and bounds from the first input cell, and destination stores/loads
   from writable-frame access; there are no execution premises. It executes
   the actual wrapper and proves the output cells equal the input cells,
   including undefined cells, with `write_prefix_at`, updated fields and
   memory framing. It retains the same explicit no-crossing restrictions and
   initial word-separation premise. This is a helper contract, not equivalence
   of any public jet to its canonical program.
   **Bound the next helper milestone by its consumers.** All 36 projection
   jets copy at most 32 bits. A helper contract for `0 < n <= 64`, at every
   valid cursor, suffices for them without narrowing any projection's input
   or frame-layout coverage. After a partial-word copy, the remaining count
   still satisfies that bound: an unaligned loop returns in its first
   iteration, while the aligned `ROUND_UWORD(n)` / memcpy path copies exactly
   one word. Prove these actual branches and pointer transitions next. A
   multi-iteration helper contract remains a later requirement for consumers
   that copy larger counts; do not count short-return results as full jets.
   **Aligned destination, first loop return completed.**
   `jet_copyBits_loop_exec.v` proves the actual loop fill and first return,
   then the complete helper call for `dst_shift = 0`, `1 <= src_shift <= 63`
   and `0 < n <= src_shift`. Its single destination store is derived from
   initial writable access, with exact value, metadata, load, permission and
   block framing. This path reads the source before storing, so it needs no
   input/output word-separation premise. It is still helper infrastructure.
   **Aligned short-copy frame cells completed.**
   `jet_copyBits_aligned_short.v:eval_copyBits_aligned_short_layout` derives
   the complete actual wrapper call from logical input cells and writable
   output frames for that case. It proves the output cells, written prefix,
   cursor update and memory framing, also for undefined cells. Its source
   word is read before any store, so the theorem preserves the helper's
   support for overlapping cell words. Source-word crossings and partial
   destination continuations remain to be assembled.
   **Do not silently model plain memcpy as a builtin.** The generated global
   declaration at `jets.v`'s `_memcpy` entry is `EF_external "memcpy"`, not
   `EF_memcpy`. `Events.extcall_memcpy_sem` therefore does not prove that call.
   No C memcpy implementation was found in the pinned CompCert runtime.
   The fully aligned path needs an explicit verified linking/model solution;
   neither an assumed external execution nor a new memcpy axiom may be hidden
   in a final jet contract. Keep this obligation visible while completing the
   loop and other non-memcpy branches. No jet is complete by excluding this
   valid input/layout case, and the existing C source/AST has not been changed.
   **Aligned destination, input-crossing loop return completed.**
   `jet_copyBits_loop_crossing.v:eval_copy_helper_aligned_full` executes the
   complete helper call for `dst_shift = 0`, `1 <= src_shift <= 63` and
   `src_shift < n <= 64`. Both stores are derived from initial writable access.
   Its next-source-word load after the first store is derived from initial
   next-word/destination separation. The theorem proves the exact joined word,
   unchanged destination fields and outside-word loads, permissions and valid
   blocks. The reusable loop-selection lemma also applies after a partial-word
   prefix. This is a single-iteration branch contract, not a general memcpy or
   public jet proof.
   **All partial-source/aligned-destination copies up to 64 bits completed.**
   `jet_copyBits_aligned_crossing.v` derives both source-word loads and address
   bounds from logical input cells, executes the crossing helper and wrapper,
   and proves equal output cells, written-prefix preservation, cursor update
   and memory framing. Its unified initial-only
   `eval_copyBits_aligned_partial_source_layout` combines both loop returns
   for every `0 < n <= 64` at those cursors. Next-word separation is required
   only when the input crosses; undefined cells are supported. Partial
   destination continuations and the external memcpy model remain outstanding.
   This is shared helper infrastructure, not additional public jet coverage.
   **Source crossing inside a partial destination word completed.**
   `jet_copyBits_partial_crossing.v:eval_copy_helper_partial_cross` executes
   the actual clear, left fill, four temporary updates (including decrementing
   the source pointer), common right fill and second short return when
   `src_shift < n <= dst_shift`. Its initial-only contract derives all three
   stores and both post-store source reads from writable access and initial
   word separation. It proves the exact joined partial word, unchanged frame
   fields and outside-word load/permission/block framing. The raw left-advance
   and right-return lemmas are reusable for remaining continuations; they are
   INTERNAL and not additional jet-equivalence results.
   **Every copy fitting the partial destination word: logical contract.**
   `jet_copyBits_partial_crossing_cells.v:eval_copyBits_partial_word_layout`
   combines the crossing path with the previously checked short path. Its
   initial-only contract covers every `0 < n <= cursor mod 64`, deriving source
   loads/bounds from logical cells and stores/cursor updates from writable
   output frames. It proves equal cells (including undefined cells), preserved
   written prefix and memory framing. Next-source-word separation is needed
   only if the source crosses. Together with the aligned-destination contract,
   the remaining non-memcpy cases are copies continuing past a partial output
   word; do not invoke a second helper on fictitiously updated frame fields.
   **Whole-buffer separation now implies each accessed-word protection.**
   `jet_copyBits_separation.v:copy_buffers_separated_words` derives the
   store/load disjointness used above from `jet_copy_buffers_separated`, for
   any input bit index within the input count and output bit index below the
   writable cursor. It supports shared cell blocks and arbitrary cursors;
   no distinct-cell-block premise or extra contextual assumption is needed.
   Reuse it for current/next source words and both destination words.
   **Common right-fill continuation completed (INTERNAL).**
   `jet_copyBits_right_advance.v:exec_copy_right_continue` executes the actual
   right fill, false short-return test, count/shift updates and destination
   pointer decrement. It includes `ss = ds`, producing shift zero rather than
   assuming this case away. Its load/store premises still need deriving from
   initial frames and composing with the subsequent loop or external memcpy.
   **Next concrete continuation decomposition (initial contracts unproved).** For
   initial shifts `ss < ds` and `ds < n <= 64`, reuse the actual left advance
   and `exec_copy_right_continue` with source shift 64, then compose the loop.
   The next loop has count `n - ds`, source shift `64 - (ds - ss)`, decremented
   source and destination pointers. Its first return suffices because
   `n - ds <= 64 - (ds - ss)`. For `ds <= ss` and `ds < n <= 64`, the next loop
   has count `n - ds`, shift `ss - ds` and a decremented destination pointer;
   reuse its first return when `n <= ss`, second return otherwise. If
   `ss = ds`, this is the plain external memcpy branch instead. Derive the
   second destination word's access from `write_frame_at`, preserve required
   source loads across every preceding store, and observe cells using the
   corresponding logical cursor split. Execute the actual updated temporaries:
   the helper has not changed either frame's stored cursor.
   **Both crossings, smaller initial source shift: actual helper completed.**
   `jet_copyBits_two_words_left.v:eval_copy_helper_two_left` derives the four
   stores from initial writable access to both destination words. Initial
   source-word separation from the first destination word preserves every
   source read after earlier stores; the final store needs no additional
   separation from its already-read source. It executes the exact partial
   prefix, updated temporaries, actual loop selection and first loop return.
   It proves both exact output words, unchanged destination metadata and
   framing outside the two-word interval. Raw statement composition lives in
   `jet_copyBits_two_words_left_exec.v`; no second helper call or changed
   stored cursor is fabricated. The `ds < ss` continuation and plain external
   memcpy branch remain outstanding, and this adds no public jet coverage.
   **Both crossings: logical wrapper contract completed for that case.**
   `jet_copyBits_two_words_left_cells.v:eval_copyBits_two_left_layout` derives
   both source loads/bounds and both destination accesses from logical input
   cells and `write_frame_at`. Word protections follow from the existing
   whole-buffer separation predicate. It executes the actual helper and
   cursor-update wrapper, proving equal cells (including undefined cells),
   prefix preservation, updated metadata and two-word/cursor memory framing.
   It covers `src_shift < dst_shift < n <= 64`; no intermediate execution or
   store premise remains. The general crossing-position/address lemmas also
   apply to the other partial-destination continuation. This is not a full
   projection-jet proof; no jet is counted by omitting remaining layouts.
   **Destination-only crossing: actual helper completed.**
   `jet_copyBits_two_words_right_short.v:eval_copy_helper_two_right_short`
   derives the complete actual helper call and all three stores when
   `0 < dst_shift < n <= src_shift`. It preserves the repeated current-source
   read using initial separation from the first destination word, executes
   the actual right-prefix/temporary advance and first loop return, and
   proves exact values in both destination words plus metadata and memory
   framing. Aligned sources (`src_shift = 64`) are supported. The reusable
   `jet_copyBits_two_words_right_exec.v` prefix/loop composition also supports
   the remaining second-loop-return case (`dst_shift < src_shift < n`).
   **Destination-only crossing: logical wrapper contract completed.**
   `jet_copyBits_two_words_right_short_cells.v` derives the actual helper and
   wrapper calls from logical initial frames and whole-buffer separation,
   for `0 < dst_shift < n <= src_shift`. It proves equal output cells,
   preserved prefix, updated cursor fields and two-word/cursor framing.
   Undefined cells and initially aligned sources are supported; no unused
   next-source-word premise is imposed. This remains shared helper progress.
   **Larger source shift, both crossings: helper and wrapper completed.**
   `jet_copyBits_two_words_right_full.v` derives all four stores and the
   next-source read after stores to both destination words, executing the
   actual second return of the first loop iteration. Its cell module derives
   word loads/access/bounds and separation from logical initial frames and
   the existing whole-buffer predicate. The actual wrapper has equal output
   cells, preserved prefix, updated metadata and two-word/cursor framing for
   `0 < dst_shift < src_shift < n <= 64`. No execution/store premise remains.
   The separately checked branch contracts now cover all positive counts up
   to 64 that do not reach plain external memcpy. Assemble their uniform
   footprint contract next; the external-library model still prevents full
   projection coverage and must not be replaced with an assumed jet call.
   **Uniform non-memcpy small-copy contract completed.**
   `jet_copyBits_small_layout.v:eval_copyBits_small_no_memcpy_layout` composes
   all checked branches for every `0 < n <= 64`, with uniform output footprint
   `[outedge + 8 * ((cursor - n) / 64), write_word_address outedge cursor + 8)`.
   It proves the actual wrapper call, equal cells, prefix/cursor observations
   and memory framing from initial frames and whole-buffer separation. Its
   explicit `~ copy_small_memcpy_case` premise excludes exactly the aligned
   source/destination path and continuation with equal initial shifts. This
   is not a general copyBits contract or a public jet proof; those valid
   layouts remain required by the goal. Next resolve the plain-library-call
   model and add its missing branch, then compose the actual leftmost/rightmost
   jet boundaries (including by-value source copies, forwardBits and frees)
   with the canonical programs. Do not add restricted-layout projection
   entries to coverage while that branch remains missing.
   **Canonical projection cells and input slices checked separately.**
   `jet_projection_cells.v:encode_leftmost` / `encode_rightmost` prove the
   exact existing canonical terms encode to the appropriate prefix/suffix,
   generically for all vector depths and output types (including sum padding).
   The frame lemmas derive those input-cell observations from the original
   full encoding, with the rightmost cursor advanced by the skipped length.
   `projection_buffers_slice` derives the smaller read-buffer separation from
   the original input count, also after skipping. No external execution or
   extra layout restriction is assumed. These are representation obligations,
   not C jet execution proofs or coverage. Explicit compilation and direct
   kernel checking passed; their eight results are also in the expanded
   126-module public assumption/type audit. Final projection calls remain open.
   **multiply_8/16/32 completed independently of the library-copy gap.**
   `jet_multiply_spec.v` defines the literal canonical Haskell composition
   with a doubled-width zero input and the existing `Word.fullMultiplier`.
   Its width-generic symbolic bridge proves the exact CompCert carrier product
   denotes that program, using the canonical output range rather than input
   enumeration. Actual body adapters retain byte-to-long casts at width 8,
   long multiplication, distinct input-reader/output-writer widths and cleanup.
   `jet_multiply8_layout.v` and `jet_multiply_wide_layout.v` discharge every
   allocation, store, reader, writer and free from initial contracts, exporting
   three named local specs, context substitution and call-boundary guarantees.
   Arbitrary valid cursors, crossings and unrelated output contents are covered.
   **full_multiply_8/16/32 completed independently.** Reuse
   `Word.fullMultiplier` directly: its base and recursive routing match the
   canonical `Programs.Arith.full_multiply`. Four actual readers feed
   `x * y + z + w`, then the doubled-width writer. The existing
   `fullMultiplier_correct` supplies the exact value and its canonical output
   range bounds the entire sum below the carrier modulus. Do not assume the
   product/sum fits without deriving that fact. The checked execution/layout
   modules extend sequencing to the fourth reader and retain the nested input
   product encoding. They export three named canonical local specs, contexts
   and call-boundary guarantees with arbitrary valid cursors and crossings.
   **Shared four-input bridge checked.** `jet_full_multiply_word.v` supplies
   `full_multiply_int64_denotes`, covering the actual left-associated carrier
   `x * y + z + w`. Each intermediate product/sum is bounded from the canonical
   output range and nonnegative remaining operands before removing its modulus.
   `frame_input_word_quad_encode` derives four logical input observations at
   successive word offsets from the exact nested-pair encoding. Both compile
   and pass direct kernel checking. These two helper results and the four-reader
   execution/layout consumers are in the expanded 126-module audit; only the
   three named complete jet contracts count as added coverage.
   `multiply_64` and `full_multiply_64` instead execute actual uint128 helpers
   and require separate adapters; do not force them into the scalar bodies.
   **parse_lock completed.** The literal `Programs.TimeLock.parseLock` is
   mapped to the existing canonical subtraction-borrow projection, with
   `Alg.scribe` for its 500000000 constant. Its real C call reads once, performs
   the mixed uint/long comparison, writes the tag and the original 32-bit word,
   and frees the by-value source copy. The sum-output encoding reuses the
   carry-plus-word writer; valid crossings and unrelated output contents remain
   general. Canonical local/context/call-guarantee results are in the expanded
   133-module audit. This C declaration is core despite its BitcoinJet catalog
   constructor; it requires no application primitive or environment model.
   **parse_sequence completed.** The expanded 140-module audit includes its
   complete C-call consumer and the preceding representation infrastructure.
   `jet_word_bit_spec.v` shares an index-parametric take/drop bit projection
   and symbolic numeric bridge. `jet_int64_bit_mask.v` proves the top-bit
   threshold and isolated-bit mask/nonzero bridges for the actual long carrier.
   `jet_parse_sequence_spec.v` mirrors the literal canonical program and proves
   its bit31/bit22 projection paths, payload decoding, actual carrier-to-program
   bridge and both sum encodings. Disabled output is a false tag followed by
   17 undefined cells; enabled output is a true tag, bit22 and the low 16 bits.
   These 18 closed results are shared representation infrastructure. The
   separate execution/layout results establish the added jet coverage.
   `jet_skipBits_layout.v` proves the actual `f_skipBits` cursor decrement
   from initial writable frame conditions, including its PRODUCTION
   assertion loop with a constant-false guard. The initial-only contract
   derives the cursor store and preserves every load outside that field,
   permissions and valid blocks. Its padding contract establishes physical
   existence of arbitrary skipped cells and preserves the output prefix;
   it does not require zero contents. `jet_parse_sequence_exec.v` executes the
   actual read, first Boolean-returning writer, conditional branch (second
   tag/write16 or skip17), true return and local cleanup. The writer module
   composes both branches, preserving the first flag also across word
   boundaries. `jet_parse_sequence_layout.v` derives the entire call from
   initial frames and exports canonical local/context/call guarantees.
   All actual shifted long masks and argument casts are retained. The audit
   has 719 results (205 closed); prior types, assumptions and the inherited
   kernel axiom list are unchanged. AST regeneration and negative gates pass.
   **Next copy-family representation bridge.** `jet_full_shift_cells.v` proves
   that canonical full-left/full-right-shift1 rebalances tuples without
   changing their serialized cells, for arbitrary element types and vector
   sizes. It has separate compilation/kernel/closed-assumption checks after
   the integrated audit, but is not in its public snapshots yet. This does
   not add full-shift jet coverage: actual copyBits paths, including the
   unspecified external memcpy paths, still require execution proofs.
   **Completed independent consumer: sha_256_iv.** The actual C helper initializes
   eight uint32 words and the enclosing jet calls the actual write32s loop.
   `jet_uint32_array_init.v` proves a reusable constant-array statement/store
   contract from initial writable permissions. `jet_sha256_iv_init.v` applies
   it to the actual f_sha256_iv function, with all eight stores, framing and
   permission/block preservation derived. Its exact canonical scribe constant
   is checked against both Digest.sha256_iv and the serialized eight words.
   These modules have explicit compilation and fresh kernel checks. The checked
   `jet_output_sequence_step.v` supplies slice-write continuation and prefix/
   cell preservation for successive writes. `jet_write32s_exec.v` executes the
   actual pointer/count loop; `jet_write32s_layout.v` derives its complete
   helper contract from the initial array and writable frame, retaining
   arbitrary output contents, cursor crossings and memory framing.
   `jet_sha256_iv_exec.v` adapts the exact generated two-local body and
   `jet_sha256_iv_layout.v:sha256_iv_local_spec` derives the complete call
   against the canonical scribe term, including both allocations, source
   copy, actual array initializer/write loop and both local frees. It exports
   context and call-boundary guarantees. Coverage is now 137/533. The expanded
   integrated audit passed on 148 modules / 757 results (222 closed), including
   negative gates and byte-identical AST regeneration. Removing the additions
   reproduces all prior contract/assumption snapshots exactly; kernel axioms
   are unchanged. Reuse the array read/write sequencing
   for subsequent hash jets; compression still needs its own verified bridge.
   **Completed next padding consumer.** `jet_left_pad_bit_wide_exec.v` /
   `jet_left_pad_bit_wide_layout.v` prove left_pad_low_1_16/32/64 with a shared
   long-carrier adapter; `jet_left_pad_bit8_exec.v` /
   `jet_left_pad_bit8_layout.v` handle the uchar variant. The specs reuse the
   exact canonical recursion in `jet_spec.v`; actual readBit, Boolean/payload
   casts, writers, allocation/copy/cleanup and all memory effects are derived
   from initial-only contracts, without cursor/output-content restrictions.
   Source compilation, fresh kernel checking and individual assumption checks
   passed. The expanded integrated audit passed on 152 modules / 775 results
   (225 closed), including negative gates and byte-identical AST regeneration.
   All earlier type/assumption snapshots and kernel axioms are unchanged.
   This milestone brought coverage to 141/533. The later right_pad_low_1_N
   and left_extend_1_N consumers below reuse its lifecycle, retaining actual
   shift/conditional expressions and distinct canonical program bridges.
   The remaining high-padding one-bit variants also use copyBits and actual
   writeBit loops; they are not arithmetic OR-expression adapters. Their
   aligned copy path can call plain memcpy even at a zero byte count, so do
   not count them from the restricted no-memcpy theorem. Larger-input padding
   retains the same documented external memcpy gap.
   `jet_pad_bit_spec.v` now supplies those literal right-padding, high-padding
   and left-extension terms, parametricity and byte/wide carrier bridges.
   Explicit source compilation and fresh kernel checking passed; all seven
   lemma assumptions are closed. Both project manifests include it; this
   module is now in public snapshots but adds no jet coverage on its own.
   For right padding, adapt the exact cast/shift/cast expression in the
   generated body and prove its 7/15/31/63 shift guards. For extension, retain
   the conditional _t'2 assignment: tint at 8/16, tuint at 32, tulong at 64.
   Its exact wide payloads are 65535/4294967295/18446744073709551615, not an
   assumed common untruncated argument. Reuse the checked readBit/writer and
   frame lifecycle; do not infer actual C calls from these pure bridges.
   **Right-padding consumers completed.** `jet_bit_word_layout.v` now factors
   the initial-only allocation/copy/readBit/write/free lifecycle. Its two
   internal contracts require an actual body adapter and an actual writer
   with canonical output/framing; both are proved for every concrete jet.
   `jet_right_pad_bit{8,_wide}_{exec,layout}.v` completes all four calls,
   including exact casts and 7/15/31/63 shift guards. Source compilation,
   fresh independent kernel checks and local-spec assumption checks passed;
   the expanded 162-module integrated audit passed. Four `left_extend_1` consumers
   now reuse this lifecycle, proving the actual conditional assignment,
   all-ones constants and casts against the literal canonical conditional
   padding program. All four compile from current source and passed fresh
   independent kernel and local-spec assumption checks. Coverage entries
   are 149/533. Internal contracts are discharged, not left as final premises.
   **Larger-input extension consumers completed.**
   `jet_extend_word8_layout.v` completes left_extend_8_16/32/64. The shared
   loop matches the actual quotient-minus-one bounds (1/3/7), conditional
   255/0 assignment, uchar writer call, increment and exit. The full adapter
   retains source copy, read8/uchar assignment, promoted signed shift/MSB
   Boolean cast, final payload write, true return and free. The initial-only
   `jet_write8_sequence.v` derives the run premise, output cells, prefix and
   memory framing. The generic canonical `left_extend_word_spec` retains
   the literal leftmost/conditional padding program and supplies a symbolic
   MSB/encoding bridge. All intermediate contracts are discharged in the
   three local specs, without output initialization or original input/output
   separation. Source compilation, independent kernel and individual
   assumption checks passed; both manifests and public lists include all five
   modules. Coverage is 153/533. Next adapt the sequence/lifecycle to
   right_extend_8_N: retain its low-bit AND/Boolean cast, payload-before-fill
   order, and literal rightmost/right-padding program. Then extend the
   reader/writer adapters to 16/32-bit inputs. These bodies do not use copyBits;
   do not introduce its external memcpy gap into their proofs.
   **Right-extension proofs checked and registered; expanded audit pending.**
   `jet_right_extend_word8_loop.v` matches and executes the actual mirrored
   `_lsb` fill loops and the low-bit AND/Boolean cast. It reuses the checked
   1/3/7 bounds and index-step evaluation, but retains an INTERNAL writer-run
   premise. `jet_int32_bit_mask.v` supplies symbolic isolated-bit masks;
   `jet_right_extend_word_spec.v` retains literal rightmost/right-padding
   terms and proves the low-bit and sequence-encoding bridges. The new
   `jet_right_extend_word8_exec.v` proves the complete entry/body/return/free
   adapter: read/normalize once, set `_lsb`, WRITE THE PAYLOAD FIRST, then
   initialize `_i` and execute the fill loop. The initial-only local specs in
   `jet_right_extend_word8_layout.v` discharge every run/free premise using
   the existing byte sequence and lifecycle proofs. All five files compiled,
   and fresh independent kernel checks passed. Each of the three local specs
   retains only the existing six assumptions; mask/canonical bridges are
   closed. Their five modules are now in both manifests/public lists; the
   three exact local specs bring registered coverage to 156/533 (377 remain).
   The expanded audit passed every gate on 179 modules / 918 results
   (275 closed); older contracts/assumptions remain byte-identical after
   removing the 23 results / 11 definitions added by this family. Continue
   with the expanded wide-extension audit below. Do not claim equivalence
   from only the pure sequence bridge or conditional loop proof.
   **Wide extension inputs completed and audited.**
   `jet_write_wide_sequence.v` derives successive actual wide-writer calls,
   encoded output, cursor changes, prefix and memory framing from initial
   permissions. The left/right `jet_*extend_wide_{loop,exec,spec,layout}.v`
   adapters cover 16_32, 16_64 and 32_64: read once into the exact unsigned-long
   carrier, evaluate the actual MSB shift or LSB mask/Boolean cast, use the
   checked signed-int/unsigned-int fill casts, execute the finite writer loop,
   return true and free the copied source frame. Left writes fill before the
   payload; right writes payload before fill. Canonical bridges reuse the
   width/depth-generic padding programs and symbolic top/low-bit facts.
   No payload enumeration or original input/output separation is needed;
   valid arbitrary cursors, crossings and unrelated output bits are retained.
   All six exact local specs compiled, passed fresh independent kernel checks
   and retain only the existing six assumptions. Pure bridges are closed.
   Nine modules / 44 results / 28 definitions are registered, bringing coverage
   to 162/533 (371 missing). Their expanded audit passed every gate on 188
   modules / 962 results (287 closed), with all older assumptions/contracts
   unchanged after removing the new declarations. The inherited 15 kernel
   axioms are unchanged; negative tests, pinned AST regeneration and the
   separate regression build passed.
   This completes the declared left/right extension family; other padding and
   shift families still require their own actual C proofs, including the
   unresolved external-copy contract where those bodies call memcpy.
   **Scalar rotations at 32/64 bits: complete canonical contracts.** The
   scalar C shift/rotate macros do not call memcpy. At 32/64 bits they read
   an 8-bit amount followed by the wide payload. The four left/right local
   specs derive entry, source copy, both reads, count arithmetic, scalar
   helper call, write, return and cleanup from initial frames. No helper,
   writer or output-value premise remains; valid arbitrary cursors, crossings,
   unrelated output bits and memory framing are retained.
   `jet_read8_wide_sequence.v` derives both actual reader calls, exact unsigned
   carriers, cast normalization, combined cursor and memory preservation from
   initial frames, reusing the total readers. `jet_rotate_wide_helper.v`
   executes the complete rotate_16/32/64 scalar helper calls with arbitrary
   carrier values and bounded counts, including the zero branch that avoids
   a shift by the full carrier width. `jet_rotate_count_exec.v` handles the actual promoted signed
   remainder and uchar cast: with a nonnegative byte carrier and positive
   width, C's signed remainder equals the required nonnegative modulus.
   The count adapter also executes the right-rotation `(bits-amt)%bits`
   expression, retaining the tint subtraction/remainder and final uchar cast.
   `jet_rotate_spec.v` and `jet_right_rotate_spec.v` retain the literal
   Programs.Word variable-control recursion, including reverse itemsOf,
   conditional rotate1, vector promotion and the final SingleV step. Their
   normalization splits control bits only, never payloads. The width-generic
   bit-composition bridge reuses `Word.rotate_const_correct_word`; the scalar
   bridge proves the actual shift/OR extraction, not a substituted numeric
   specification. The right family shares displacement, reader, writer,
   helper and scalar bit lemmas with the left family.
   All four local specs compiled and passed fresh independent kernel checks.
   The left family and shared helpers passed the complete integrated audit
   on 197 modules / 1004 results (315 closed), adding 42 results and 23
   definitions without changing older snapshots or the 15 inherited kernel
   axioms. The right-family expanded audit passed every gate on 203 modules /
   1024 results (326 closed), including negative fixtures and pinned AST
   regeneration. Its 20 added results / 9 definitions preserve the older
   snapshots exactly; the 15 inherited kernel axioms remain unchanged, with
   no unsafe recursion, assumed positivity or type-in-type. The separate
   regression build passed. Coverage is 166/533 (367 missing), not completion.
   **Scalar rotations at 16 bits: completed and audited.** Smaller rotations
   read a four-bit amount. The `jet_read4_*.v` modules prove the
   actual non-crossing/crossing branches, total initial-frame execution,
   exact unsigned Word4 interpretation, cursor increment and memory framing,
   including a mixed read4-plus-wide reader contract.
   Both canonical rotate_16 contracts derive the whole actual C call from
   initial frames, with arbitrary valid cursors, crossings, output contents
   and memory framing. They retain `% 16` and the uchar cast even though the
   nibble range makes the modulus an identity. `jet_rotate_control_word.v`
   shares the symbolic bit-composition bridge across control widths and
   directions; `jet_rotate16_spec.v` retains the literal canonical program
   whose control list is exhausted before SingleV.
   The expanded audit passed all gates on 216 modules / 1061 results (344
   closed), adding 37 results / 17 definitions. Removing just those additions
   reproduces the previous assumption and contract snapshots byte-for-byte.
   The inherited 15 kernel axioms are unchanged. Negative tests, pinned AST
   regeneration and the separate regression build passed. Coverage is
   168/533 (365 missing), not completion.
   **Byte rotations: complete canonical contracts and expanded audit.**
   `jet_rotate8_*.v` and `jet_read4_byte_sequence.v` compile end-to-end source
   proofs and passed a fresh final independent kernel check. Individual local
   specs retain the existing six assumptions and the pure machine/canonical
   bridge is closed. Nine modules / 31 results / 17 definitions are registered.
   Their expanded audit passed all gates on 225 modules / 1092 results (361
   closed). Removing the 31 added results / 17 definitions reproduces the
   previous assumptions and public contracts byte-for-byte; the inherited
   15 kernel axioms are unchanged. Negative tests, pinned AST regeneration and
   the separate regression build passed. This completed audit covers 170/533
   (363 missing), not completion. The helper executes the actual unsigned left and
   signed right promotions, with uchar truncation. Its low-bit bridge is
   symbolic and does not assume signed shift equals unsigned shift. The
   literal canonical Word4 control program retains its final SingleV identity
   step; normalization splits only the 16 control values, never the payload.
   No helper execution, writer or output-value premise remains in the final
   local contracts. Do not count reader/helper lemmas as jets or weaken frames.
   **Zero-fill byte shifts: complete canonical contracts; integrated audit passed.** Reuse the exact nibble/byte-control reader sequences
   and frame lifecycle, but inspect each helper's out-of-range count branch.
   Shift semantics are not rotation modulo semantics. Preserve signed/unsigned
   promotions, optional fill inputs and canonical final SingleV behavior; prove
   the actual helper before connecting its result to the literal shift program.
   `jet_shift8_expr.v` stages the exact two generated byte helper body shapes
   and expression evaluation for the count comparison, signed right shift,
   unsigned multiply-by-one left shift, double uchar cast and fill XOR. The
   source and fresh independent kernel check passed. The now-registered
   `jet_shift8_helper_exec.v` executes both complete helpers through internal
   reader/writer contracts, including both fill values and all count branches.
   Reader arguments are the `_src` pointer parameter, not an address of a local
   struct. `jet_shift8_exec.v` and `jet_shift8_layout_machine.v` derive both
   zero-fill wrapper calls from initial frames, retaining crossings, arbitrary
   output bits and memory framing. No helper execution or writer premise
   remains in their final contracts.
   `jet_shift_spec.v` mirrors the literal canonical left/right_shift_with
   recursion, including consuming all remaining controls at SingleV and
   duplicating the fill value at vector promotion. `jet_shift8_spec.v` uses
   this program with a false fill. Its checked normalization splits 16 control
   values and exposes only the payload's product structure, never its bit
   values. Direct conversion timed out at count 7; exposing that structure and
   simplifying before conversion avoids the expansion and compiles in under
   one second with the original 10-second tactic limit.
   The machine bridge is symbolic, retains Int.shr for the right helper and
   covers zero outputs at counts >=8 without count modulo. Both exact local
   specs passed fresh kernel and individual assumption checks (existing six
   assumptions; pure bridge closed). Eight modules / 33 results / 24 definitions
   are registered, bringing entries to 172/533 (361 missing); their expanded
   integrated audit passed all gates on 233 modules / 1125 results, including
   negative tests and pinned AST regeneration. Earlier snapshots are unchanged.
   **Fill-controlled byte shifts: complete canonical contracts; integrated audit passed.**
   `jet_readBit4_byte_sequence.v` derives exact bit/nibble/byte reads, 13-bit
   non-wrapping cursor advance and memory observations. `jet_shift8_with_exec.v`
   executes the real wrappers with readBit and a Boolean cast; the helper uses
   the checked fill/count proof. `jet_shift8_with_layout_machine.v` derives all
   calls and frame lifecycle from initial frames. `jet_shift8_with_spec.v`
   retains the literal canonical program and proves its complement normal form
   without payload enumeration. `jet_shift8_with_word.v` proves exact carrier
   representation (decoding alone is insufficient for the second XOR).
   `jet_shift8_with_denotes.v` connects the decoded result to that program.
   Both named specs in `jet_shift8_with_layout.v` passed fresh kernel and
   assumption checks (same six inherited assumptions; pure bridges closed).
   Eight modules / 23 results / five definitions are registered, bringing
   entries to 174/533 (359 missing). The expanded audit passed all gates on
   241 modules / 1148 results (392 closed), including negative tests and pinned
   AST regeneration. Earlier snapshots and inherited kernel axioms are unchanged.
   The registered `jet_shift8_fill_word.v` supplies complement involution,
   exact low-byte fill-XOR bits and exact unsigned representation of the
   complemented canonical word. Its source and fresh independent kernel check
   passed; the checked representation and involution results are closed.
   These value lemmas support fill-input proofs but add no coverage by themselves.
   **Zero-fill 16-bit shifts: complete canonical contracts; integrated audit passed.** The 16-bit
   helper reads its count with read4, its payload with read16 into Vlong and
   writes through write16. There is no payload uchar cast. The right shift
   is unsigned Int64.shru, unlike the promoted signed Int.shr byte helper;
   the left multiply-by-one and final tulong cast remain in the actual AST.
   Counts from read4 are <16 but both helper count branches must still be
   accounted for in reusable execution. Adapt actual ASTs while sharing
   canonical controls and reader/writer contracts; do not substitute a
   mathematical shift specification or merely rename the byte carrier.
   `jet_shift_wide_expr.v` is registered shared infrastructure:
   exact body shapes for all six LP64 helpers and shared scalar, fill and
   count expression evaluation. Source and fresh independent kernel checks
   passed. The width-specific fill constants retain their actual C types:
   signed int 65535, unsigned int -1, unsigned long -1.
   `jet_shift_wide_helper_exec.v` now executes all six actual helpers through
   internal reader/writer contracts, both fill flags and every count branch.
   `jet_shift_wide_exec.v` executes their six zero-fill public wrappers;
   these internal results alone are not jet coverage. The 16-bit initial-frame
   theorem in `jet_shift16_layout_machine.v` discharges all internal calls,
   allocations, copies, writes and cleanup. `jet_shift16_spec.v` retains the
   literal canonical program, normalizing only the 16 controls with symbolic
   payload bits. `jet_shift_wide_bits.v` proves the shared low-bit branch bridge,
   including shifts past the logical/carrier width and no count modulo.
   `jet_shift16_word.v` connects the writer's decoded value to the canonical
   program. Both named specs in `jet_shift16_layout.v` passed fresh kernel and
   assumption checks (same six inherited assumptions; pure bridges closed).
   Eight modules / 27 results / 21 definitions are registered, bringing entries
   to 176/533 (357 missing). Their expanded audit passed every gate on 249
   modules / 1175 results (404 closed), including negative tests and pinned AST
   regeneration. Earlier snapshots and inherited kernel axioms are unchanged.
   **Fill-controlled 16-bit shifts: complete canonical contracts; integrated audit passed.** Reuse the
   complete helper with the bit-read flag, derive a bit/read4/read16 sequence
   from initial frames and inspect both fill toggles. Unlike the byte helper,
   wide left shifts can retain upper bits until writing: prove the second
   XOR's low bits directly, rather than asserting a false exact truncated
   carrier equality. For 32/64-bit consumers use read8 controls and the existing
   read8/wide sequence; retain >=width zero-fill behavior and final SingleV
   controls in the canonical program. Extend the canonical normalization
   structurally if exhaustive control normalization becomes expensive; do
   not enumerate payload values or replace the program by a mathematical spec.
   Four registered fill-consumer modules now compile and passed fresh kernel
   checks: `jet_shift_wide_fill_word.v` supplies the exact initial complement
   carrier and arbitrary-carrier low-bit XOR fact; `jet_shift16_with_spec.v`
   retains the literal fill program and normalizes only fill/control values;
   `jet_readBit4_wide_sequence.v` derives the bit/read4/wide reader sequence
   from initial frames; `jet_shift16_with_word.v` proves low-bit and decoded
   payload equivalence. Its value bridges and the fill normal form are closed.
   These helpers add no coverage by themselves. `jet_shift_wide_with_exec.v`
   now executes all six actual fill wrappers through their readBit and helper
   calls. `jet_shift16_with_layout_machine.v` composes the 21-bit initial
   W16 input/frame lifecycle. `jet_shift16_with_layout.v` connects the decoded
   result to the canonical program and exports both named local specs,
   context results and call-boundary guarantees. Every source and fresh kernel
   check passed; named local specs retain the existing six assumptions and
   value bridges are closed. Seven modules / 20 results / five definitions are
   registered, bringing entries to 178/533 (355 missing). Their expanded audit
   passed every gate on 256 modules / 1195 results (414 closed), including
   negative tests and pinned AST regeneration. Earlier snapshots and inherited
   kernel axioms are unchanged. The bit read precedes the count/payload helpers, so the count
   begins at rc+1, payload at rc+5, and the final copied cursor is rc+21.
   **32/64-bit zero-fill and fill-input shifts: complete and audited.**
   `jet_shift_byte_layout_machine.v` shares the
   zero-fill initial-frame lifecycle; `jet_readBit8_wide_sequence.v` derives
   exact bit/read8/wide calls; `jet_shift_byte_with_layout_machine.v` shares
   the fill-input lifecycle. Reusing `byte_rotate_size` only selects W32/W64:
   these theorems execute shift functions, not rotation functions. Canonical
   adapters in `jet_shift{32,64}_spec.v` normalize byte controls with symbolic
   payloads. The corresponding `_word.v` and `_layout.v` discharge the value
   bridges and export named local specs, contexts and guarantees. The `_with_`
   counterparts retain the literal fill-input canonical programs and low-bit
   XOR bridges. All sources and fresh independent kernel checks passed.
   Named specs retain the existing six assumptions; value bridges are closed.
   Fifteen modules / 49 results / six definitions add eight coverage entries:
   186/533 (347 missing). The expanded integrated audit (`87578`) exited 0
   through all gates on 271 modules / 1244 results (436 closed), including
   negative fixtures and pinned AST regeneration. Removing only these new
   entries reproduces the `8ef795b` snapshots byte-for-byte; inherited kernel
   axioms are unchanged. This completes the variable-shift family, not every jet.
   **Normalization lesson:** aggregate `cbn`/repeated rewriting is too slow
   for the fill64 tuple. Measured lazy reduction plus component-wise `f_equal2`
   solves the same four cases in 0.14s instead of 7s. The combined 1024-case
   theorem still timed out at `Qed`; four separately checked 256-control
   lemmas close it under the unchanged 10-second default. Do not increase
   timeouts blindly or enumerate payload values. Keep non-wrapping cursor
   bounds, >=width behavior and final SingleV controls intact.
   **Division C-side infrastructure: checked, not jet coverage.** Seven new
   modules (`jet_division_value.v`, `jet_division{8,_wide}_{expr,exec}.v`,
   `jet_division{8,_wide}_layout_machine.v`) compile and passed fresh independent
   kernel checks. The value/representation bridges are closed; both initial-
   frame execution theorems retain the existing six assumptions. They derive
   actual divide/modulo calls at 8/16/32/64 bits, arbitrary cursors/crossings,
   output preservation and cleanup. The byte body uses promoted signed
   Int.divs/mods; byte ranges exclude the signed-overflow guard and identify
   Z.quot/rem with nonnegative Z.div/mod. Wide bodies use unsigned Int64
   divu/modu. Zero is branched away before arithmetic, returning quotient
   zero and remainder input. These are numerical machine observations, NOT
   canonical jet specifications. All eight divide/modulo jets remain uncovered.
   These seven modules / 21 results / 19 definitions are now registered in
   both manifests and public lists, with NO coverage additions. Their expanded
   helper audit (`27757`) exited 0 through all gates, negative fixtures and
   pinned AST regeneration: 278 modules / 1265 results (447 closed).
   Removing only the 21 results / 19 definitions reproduces the `7e90c02`
   snapshots byte-for-byte; inherited kernel axioms are unchanged. Coverage
   remains 186 entries: none of these numeric helpers is a canonical jet proof.
   **Shared canonical full-shift bridges.** `jet_vector_shift_word.v` proves
   value conservation and quotient/remainder observations of the literal
   Word.full_left/right_shift1 programs for arbitrary ToZ base items.
   `jet_full_shift_spec.v` casts nested Word vectors to ordinary Word types,
   proves numeric preservation of those casts, and exports parametric canonical
   full-shift adapters with both numeric projections. No proof irrelevance or
   new axiom is needed for these transports: product equality is transparent.
   Both sources and fresh kernel checks pass; every new result/definition has
   a closed assumption check. The two modules / 24 results / six definitions
   are registered without coverage additions. Integrated audit `76184` exited
   0 through all gates, negative fixtures and pinned AST regeneration on
   280 modules / 1289 results (471 closed). Removing only these entries
   reproduces the `723ec34` snapshots byte-for-byte; kernel axioms are unchanged.
   **Recursive normalization is checked.** `jet_division_shift_step.v`
   derives both guard bounds from the literal is_zero/leftmost composition
   and proves exact pre/post shift observations. `jet_division_normalize_spec.v`
   mirrors divPreShift/divPostShift, including each recursive vectorComp cast,
   and proves parametricity, common scaling of numerator/divisor, normalized
   divisor bound, preserved numerator bound, remainder inverse scaling and
   agreement of the pre/post normalized divisors. Its plain-input theorem
   prepends the canonical zero word and derives the required bounds for every
   nonzero divisor. Both sources and fresh kernel checks pass; all 38 new
   results / ten definitions are closed. They are registered without coverage
   additions. Expanded audit `13659` exited 0 through all gates, negative
   fixtures and pinned AST regeneration: 282 modules / 1327 results (509 closed).
   Removing only these two modules' entries reproduces the `ef3ec4d` snapshots
   byte-for-byte; the 15 inherited kernel axioms are unchanged.
   **Canonical division recursion and eight C consumers are checked.**
   `jet_division_core_spec.v` retains the literal Programs.Arith programs,
   with named approximation/body/loop0/loop1/loop2 components. The new
   `jet_division_correction_spec.v` proves the actual corrections and overflow
   bypass; `jet_division_approx_spec.v` proves both approximation branches and
   residual bounds from the smaller-call contract. `jet_division_recursive_spec.v`
   discharges that contract by symbolic induction for every width and both
   successive div3n2n calls. `jet_division_result_spec.v` connects pre/core/post
   through common scaling and Euclidean uniqueness, including zero divisors
   and the invalid div2n1n all-ones fallback. No wider payload enumeration or
   division identity is assumed. These canonical bridges are closed.
   `jet_division_layout.v` exports named C divide/modulo local specs at
   8/16/32/64 bits, plus shared context and call-boundary guarantees. Its
   initial-frame execution consumers retain arbitrary cursors/crossings,
   initial output contents and memory framing. Current-source coqc, explicit
   static/assumption checks and fresh kernel check `47007` passed. Local/context
   results retain the existing six assumptions; guarantees add only the
   existing two Events property assumptions. All six modules / 68 results /
   21 definitions and eight coverage entries are registered. Expanded audit
   `28051` finished with exit 0: all gates, negative fixtures and pinned AST
   regeneration passed (288 modules / 1395 results, 561 closed). Removing only
   these six modules' additions reproduces baseline `c5e084d` assumptions and
   contracts byte-for-byte; all 15 inherited kernel axioms are unchanged.
   **Divides and div_mod C consumers are independently checked.**
   `jet_divides_spec.v` reuses the modulo observation, swaps operands and
   connects the actual zero test to the canonical is_zero program.
   `jet_divides_expr.v` preserves the generated byte promotions and LP64
   mixed-type comparison. The byte and shared wide execution/layout modules
   export four named initial-only local specs, context results and guarantees.
   Fresh current-source kernel checks `91259` (byte) and `41685` (wide) passed;
   the five pure bridges are closed, local/context contracts retain only the
   inherited six assumptions, and guarantees retain the two Events properties.
   Six modules / 26 results / 16 definitions / four entries are registered.
   Full audit `24374` finished with exit 0: all gates, negative fixtures and
   pinned AST regeneration passed (294 modules / 1421 results, 568 closed).
   Removing just the six new modules' assumptions/contract blocks reproduces
   `f15a9a6` byte-for-byte; all 15 inherited kernel axioms are unchanged.
   The six `jet_divmod{_expr,_representation,8_exec,_wide_exec,
   8_layout,_wide_layout}.v` modules also pass current-source coqc, explicit
   static and assumption checks, plus fresh kernels `28975` (scalar execution),
   `75385` (byte consumer) and `8206` (wide consumer). They reuse the existing
   byte/wide sequence writers, preserving quotient output during the remainder
   write, and recover the complete literal div_mod pair from its checked
   projections. All zero divisors and initial frame/layout guarantees remain.
   They are registered with four coverage entries. Expanded audit `64579`
   exited 0 through all gates, negative fixtures and pinned AST regeneration
   against accepted baseline `c27d813`. The audit also includes six new 96/64
   helper modules (12 modules / 48 results / 25 definitions added in total):
   306 modules / 1469 results, 588 closed. Removing only these 12 modules'
   additions reproduces the accepted baseline byte-for-byte.
   `exec_divmod8_choose` starts the new result contract block; `divmod8_choose`
   starts the new definition block. All 15 inherited kernel axioms are unchanged.
   **Next: DivMod128_64 and its div_mod_96_64 helper.** The canonical
   numeric bridge is now proved; do not restart normalization or replace
   the actual program with division_numeric. Reuse division_word_representation
   and div_mod_word_numeric, plus the existing reader/writer/frame contracts.
   A recurring Coq pitfall is convertible-but-differently-annotated function
   arguments in rewrites: the recursive/result proofs capture the literal
   call or guard from the goal, then use explicit exact contracts. Normalize
   only projections/types; do not unfold recursive arithmetic to repair this.
   For positivity, use direct sum/product lemmas rather than nia over a large
   context containing unrelated cubic equations.
   **Complete 96/64 helper, not yet DivMod128_64 jet coverage.**
   `jet_divmod96_arith.v` proves clipped-estimate residual bounds, exact guard,
   safe corrections, two-correction termination bound and exit balance.
   `jet_divmod96_value.v` connects CompCert shifts/masks, short-circuit comparison
   and the final modular expression to exact unsigned observations.
   `jet_divmod96_init.v` derives normalized divisor parts and the clipped
   machine quotient's invariant. `jet_divmod96_expr.v` executes the actual
   scalar trees and guard; `jet_divmod96_step.v` executes the quotient load/store
   and rh/d updates. `jet_divmod96_loop.v` supplies exit and taken-iteration
   composition rules. Their store and recursive-tail premises are discharged
   by `jet_divmod96_loop_layout.v`: fuel induction on the exact machine
   invariant gives actual loop execution, unchanged unrelated temporaries,
   framing, permissions and nextblock. `jet_divmod96_init_exec.v` executes
   the literal LP64 initialization, including its casts and multiply-by-one.
   `jet_divmod96_init_layout.v` establishes the exact initial machine values
   and invariant. `jet_divmod96_layout.v` proves whole function entry/body/free
   and the final remainder store from normalized inputs and writable,
   nonoverlapping eight-byte output slots. It needs neither initial output
   loads nor a supplied store/loop/call execution premise.
   Current-source coqc, scans and fresh kernels passed (`63181`, `81516`, `1580`,
   `82032`, `20160`). Pure numeric checks are closed; C executions retain only
   inherited assumptions. The four whole-helper modules pass fresh kernels
   (`20675`, `97397`, `27636`, `71368`). Integrated audit `4478` exited 0
   through all gates, negative fixtures and pinned AST regeneration against
   accepted baseline `35d87e1`: four modules / 15 results / 15 definitions
   added, 310 modules / 1484 results (595 closed). Removing only those additions
   reproduces both baseline snapshots byte-for-byte; all 15 inherited kernel
   axioms are unchanged. No DivMod128_64 inventory entry has been added.
   For the whole memory-aware helper, use B=2^32, D=bh*B+bl, N=ah*B+al,
   q0=min(ah/bh,B-1), delta0=N-q0*D. Maintain q=q0-i, rh=ah-q*bh,
   d=q*bl, delta=N-q*D=delta0+i*D, 0<=rh<=ah<2^64 and 0<=d<2^64.
   The guard is equivalent to delta<0; its first test ensures the second
   expression cannot overflow. Each taken body increments delta by D and
   cannot underflow the quotient/difference or overflow rh. Unroll at most two
   iterations (already proved), deriving every store from writable nonoverlapping **eight-byte**
   output slots and preserving other memory. In pinned LP64 Clight,
   uint_fast32_t is tulong; do not model the quotient slots as four-byte tuint.
   Then compose the helper calls for ah*B+am and r1*B+al. Connect their combined
   balance to **div2n1n_word_spec 6**, the CoreJets.DivMod128_64 target, using
   normalized observation/injectivity; use div2n1n_invalid_result on the other
   branch. The valid C branch has three actual writers (32,32,64), not two
   64-bit calls; the invalid branch has two 64-bit all-ones writes. Derive four
   readers, local allocations/free and branch-specific writers from initial
   frames. Reuse arithmetic invariants rather than attempting lockstep execution
   between the C loop and canonical correction combinators.
   **128/64 consumers already checked independently; initial-only integration remains.**
   `jet_divmod128_helpers.v` derives both actual helper calls, protects the
   high quotient during the second call and proves their combined balance.
   `jet_divmod128_spec.v` connects valid machine results to the literal
   div2n1n program by its checked Euclidean observation and word injectivity;
   it also proves the canonical invalid-input all-ones result and exact guard
   agreement. These canonical bridges are closed. `jet_divmod128_expr.v`
   executes the actual short-circuit guard and derives both helper preconditions.
   `jet_divmod128_entry.v` executes the four allocations, source-copy/reader
   boundaries, local reloads and both static helper call boundaries without
   hardcoded symbol blocks. `jet_divmod128_exec.v` checks the complete generated
   body outline by reflexivity, executes both branch compositions and composes
   all four reads, guard, branch, return and local free into the public call.
   Its intermediate call/free/branch premises must still be discharged; it
   is NOT an initial-only public contract or inventory entry.
   `jet_divmod128_readers.v` now derives the actual 64/32/32/64 reader sequence
   from four initial words, with exact values, crossings, framing and permissions.
   `jet_divmod128_free.v` derives cleanup from freeable permissions in the
   actual blocks_of_env order: source(16), qh(8), ql(8), r(8).
   `jet_write_wide_mixed_sequence.v` derives varying-width writers from one
   initial frame. Its run exposes protected local-load preservation at EVERY
   intermediate call, needed because C reloads ql and r between writes.
   Current-source compilation, explicit scans and fresh kernels passed for
   these eight modules (`31794`, `97721`, `39701`, `65271`, `25207`, `15804`,
   `89177`, and `20250` for the strengthened mixed run). Eight modules /
   27 results / 19 definitions are registered, without a coverage addition.
   Expanded audit `97656` completed with terminal exit 0, all gates, negative
   fixtures and exact pinned AST regeneration: 318 modules / 1511 results
   (607 closed). Removing assumptions for the eight modules and the new contract
   blocks (results start at wide_mixed_bits_nonnegative, definitions at
   wide_mixed_bits) reproduces accepted `b59bef9` byte-for-byte; the 15 inherited
   kernel axioms are unchanged. The snapshots are accepted.
   **Initial-only integration now checked independently and registered.**
   The modules `jet_divmod128_allocate.v`, `jet_divmod128_branch_layout.v`,
   `jet_divmod128_initial.v` and `jet_divmod128_layout.v` derive all four fresh
   allocations, source copy, four readers, both helper/writer branches and
   actual local cleanup from initial frames. `divmod128_local_spec` is the
   complete public C-to-canonical-div2n1n theorem; context replacement and both
   call-boundary guarantee exports also compile. Fresh kernels `18978`, `19483`,
   `63010`, `64639` passed, with explicit scans and only inherited assumptions.
   No zero-output, fixed-cursor or non-crossing premise was introduced.
   These four modules / nine results / four definitions and the named public
   coverage entry are registered. Inventory bookkeeping is now 203/533, 330
   missing; the complete expanded audit must pass before accepting its snapshots.
   Expanded audit `39496` completed with terminal exit 0: all gates, negative
   fixtures and exact pinned AST regeneration passed on 322 modules / 1520
   results (610 closed). Filtering these four modules' assumptions and their new
   contract blocks reproduces accepted `cd7d4ee` byte-for-byte; all 15 inherited
   kernel axioms remain unchanged. Accept these snapshots. This establishes
   audited DivMod128_64 coverage, not completion of the every-jet goal.
   **multiply_64 now independently checked and registered.** Ten new
   modules prove the actual 32-limb umul128 algorithm and machine operations,
   complete secp256k1_umul128/u128_mul calls, actual lo/hi struct fields and
   getters, write128's getter/writer/getter/writer order, the literal canonical
   multiply bridge, two-local lifecycle and complete public multiply64_local_spec.
   The intermediate low-field reload is protected across the first writer;
   arbitrary original frames/cursors/crossings/output bits remain supported.
   Fresh kernels passed for all modules (`59569`, `89699`, `32146`, `34160`,
   `52025`, `20300`, `21748`, `99795`, `43991`, `98186`), with explicit scans
   and only inherited assumptions. Their 39 results / 27 definitions
   and named public entry are registered (204/533, 329 missing); run the expanded audit (332 modules /
   1559 results). Only the complete public theorem counts as added coverage.
   Audit `54062` completed with terminal exit 0 through all gates, negative
   fixtures and exact pinned AST regeneration (332 modules / 1559 results,
   632 closed). Filtering the ten added modules and their new contract blocks
   reproduces accepted `027ee37` byte-for-byte; all 15 inherited kernel axioms
   remain unchanged. Accept these snapshots: multiply_64 is integrated.
   **full_multiply_64 now independently checked and registered.** Six
   new modules prove the low-word carry/balance, both actual accumulator stores
   and intervening reloads, a width-generic initial-only four-reader sequence,
   the actual body adapter, canonical fullMultiplier64 representation and
   complete public full_multiply64_local_spec/context/guarantees. All initial
   frame generality is retained; no intermediate execution is assumed by the
   public theorem. Source checks, scans, pure closed-assumption checks, inherited
   execution assumptions and fresh kernels passed (`17745`, `1861`, `29082`,
   `81459`, `62488`, `69092`). After accepting multiply64 audit `54062`, these
   six modules and three SHA context support modules are registered: 29 new
   results / 19 definitions and one public entry (205/533, 328 remaining).
   Run the expanded audit on 341 modules / 1588 results. Helpers alone do not
   count as coverage. The canonical output range bounds both accumulations.
   Audit `52561` completed with terminal exit 0 through every gate, negative
   fixture and exact pinned AST regeneration. Filtering the nine added modules
   and their contract blocks reproduces accepted `87d0082` byte-for-byte;
   the inherited kernel axiom list is unchanged. Accept the snapshots:
   full_multiply_64 is integrated (205/533, 328 remaining).
   Avoid vm_compute in an open memory context; compute only closed identifier
   lists/AST metadata, and isolate unrelated nonlinear hypotheses before nia.
   Subsequent div_mod calls require two writers with intermediate memory;
   divides swaps operands and writes one bit. A source-comment trap: the
   Haskell divides documentation says divides(0,y) is True, but its actual
   modulo-plus-is_zero composition and the C branch test whether y is zero.
   Follow the executable canonical program, not that prose claim.
   Static full-left/right-shift jets are a separate family: their fill input
   and shifted-out output are fixed-width words, not variable byte controls.
4. **Failure-capable jets: first complete consumer.** `jet_partial.v` adds
   an initial-only `jet_partial_local_spec` tied to option/assertion semantics.
   It determines the return value on every input, retains successful canonical
   output/prefix/cursor observations and bounds memory effects on failure.
   The inventory accepts named audited instances of this contract only for
   their exact C function; negative tests reject helper and wrong-function
   entries. Do not force partial specifications into total functions or assume
   away failures. `verify` is completed: its actual body copies the source frame, reads one bit
   and returns that Boolean without a writer. Its canonical specification is
   `Programs.Bit.verify` (`iden &&& unit >>> assertr cmrFail0 oh`), interpreted
   in option/assertion semantics. Cover both true and false inputs, zero output
   width, and preservation of all pre-existing memory loads are proved.
   Both returns have deterministic small-step call-boundary guarantees.
   The current Core-only positive-output context theorem does not apply to
   assertions or zero-output terms; no context-translation result is claimed
   for verify. This does not limit its individual C-to-assertion equivalence.
   Next reuse the contract for failure-capable cryptographic/application jets,
   extending their environment and failure-memory observations as needed.
5. **Hashing, secp256k1 and application primitives.** Reuse the library and
   existing cryptographic verification lemmas where they actually apply.
   `jet_read32s_exec.v` proves the actual pointer/count loop, and
   `jet_read32s_layout.v:eval_read32s_layout` derives every reader call,
   exact array value, store and cursor update from initial input/permissions.
   `jet_word32_chunks.v` converts canonical word encodings to those per-chunk
   input predicates, with symbolic length and injectivity proofs. Source
   compilation, fresh independent kernel checks and the expanded integrated
   audit passed on 165 modules / 843 results (246 closed).
   Those helpers alone add no coverage. They now support the completed
   `jet_eq256_layout.v:eq256_local_spec`: fresh source/16-word-array allocation,
   actual source copy and read32s loop, eight comparisons with early return,
   bit write, true return and both local frees. The array result is connected
   symbolically to `equality_spec (Word 8)` through chunk and carrier
   injectivity. All intermediate contracts are discharged from initial frames;
   arbitrary valid cursors, crossings, output contents and memory framing are
   retained. No original input/output separation is assumed. The comparison
   proof executes the actual loop, not an assumed numerical equality test.
   Next reuse canonical chunks/read32s for other array-consuming C jets, while
   deriving their own operations, writers, allocation and cleanup contracts.
   `Simplicity/SHA256.v:hashBlock_correct` connects a Simplicity term to VST's
   functional SHA model, not the full generated C jet call; it is support for
   a future C-to-Simplicity proof, not an additional covered jet. Likewise,
   committed `jets_secp256k1.v` avoids one AST-generation step but does not
   itself establish jet equivalence. Check artifact provenance and configuration
   before using it. Bitcoin/Elements require concrete environment representations,
   their primitive semantics, failures and suitable generated C artifacts.
   **Context initialization independently completed.**
   `jet_sha256_ctx8_init_layout.v:sha256_ctx8_init_local_spec` now derives the
   complete actual public call against literal ctx8Init, including five local
   allocations, every initializer store, both 88-byte context copies, the
   830-cell writer, return and cleanup. Fresh current-source/kernel checks pass;
   registration followed the accepted context-writer audit `45575`. Shared typed
   By_copy field preservation and size-parameterized four-local lifecycle
   lemmas avoid duplicating those obligations in later consumers. This is one
   public jet, not coverage for context add/finalize/compression.
   **Byte-array and buffer reader support independently checked.**
   `jet_read8_input_word_total.v` bridges logical byte input bits to the actual
   byte reader symbolically, including crossings. `jet_read8s_{exec,layout}.v`
   derives the complete actual byte-array loop, every read and byte store,
   exact array observations, cursor advancement and memory/permission framing
   from initial contracts. `jet_buffer_input.v` decomposes canonical balanced
   vectors and Buffer63 encodings into absent/present chunks and supplies a
   shared input-cell preservation lemma. The actual reader loop branches,
   halving update, entry, initial len store and return are retained in
   `jet_read_buffer8_{exec,call}.v`. Its present branch has an initial-only
   consumer (`jet_read_buffer8_present_layout.v`), and the complete empty
   Buffer63 call has an initial-only consumer
   (`jet_read_buffer8_empty_layout.v`). The pointer is unused in the all-absent
   case, so that consumer imposes no unused output-array permission assumption.
   All eight modules / 38 results / 20 definitions pass source, scan, assumption
   and fresh combined kernel checks (`28720`). They add no public jet coverage
   and remained unregistered pending the context-init integration acceptance.
   The old audit handle disappeared after its observed contract-gate success;
   its final result was not recovered. Remaining negative/AST checks are being
   rerun in `33472`, with a durable log at
   `/tmp/jet-audit-recovery.qWC9in/remaining-gates.log`. That recovery subsequently
   passed with terminal exit 0; prior snapshot filters and inherited axioms are
   unchanged. Context-init integration is accepted, not inferred from the lost
   handle. The support batch is now registered for its own expanded audit
   against accepted context-init baseline `b941abc`, in dependency order.
   No coverage row is added.
   `jet_buffer_chunks.v` and `jet_read_buffer8_tag_layout.v` additionally prove
   arbitrary canonical chunk capacities/widths, previous-byte array preservation
   and the actual tag read for either branch, retaining exact payload cells.
   Both pass source/scan/assumption and fresh kernel checks (`32751`, `8151`).
   The ten reader-support modules total 54 results / 28 definitions;
   their integrated audit `51817` passed all gates, negative fixtures and exact
   AST regeneration: 369 modules / 1703 results, 706 closed, still 206 jets.
   **Complete arbitrary Buffer63 reader independently checked.**
   `jet_read_buffer8_chunk_layout.v` derives either actual chunk branch from
   initial cells; `jet_read_buffer8_loop_layout.v` composes every mixed chunk,
   preserving previous output bytes and unread cells; `jet_read_buffer8_layout.v`
   derives the full actual call, initial len=0 store and return. These three
   modules / 8 results / 1 definition pass current-source compilation, explicit
   scan, assumptions and fresh kernel checks (`18859`, `22733`, `92150`). They
   are now integrated through audit `13723` and add no public coverage.
   Private array/frame/length block separation must still be derived from
   allocations in public consumers, not imposed on original input/output.
   `jet_write8s_{exec,layout}.v` additionally derives the actual byte-array writer
   loop from initial arrays and writable frames, including its uchar cast,
   pointer/count updates and return. It shares byte encodings and the existing
   prefix/sequence framing lemmas, and proves exact canonical byte output
   symbolically. Both modules / 13 results / 5 definitions pass compilation,
   explicit scans, assumptions and fresh kernel `1327`; no new assumptions.
   The five complete mixed-reader/byte-writer modules are now registered for
   expanded audit `13723` (374 modules / 1724 results, 716 closed) against
   `0ddec7c`; all gates, negative fixtures and exact AST regeneration passed.
   Three further modules / 10 results / 1 definition pass source,
   scans, assumptions and fresh kernels (`31906`, `13689`):
   `jet_output_cells_step.v` recovers writable continuation after arbitrary
   nonempty encoded cells, including the partially written boundary word;
   `jet_present_buffer_segment.v` derives a true tag plus exact byte payload;
   `jet_write_buffer8_exec.v` retains the actual length comparison, either
   branch, pointer/length updates and shared halving step. Internal branch
   adapters remain conditional until a total consumer derives their calls.
   `jet_write_buffer8_chunk_layout.v` now derives either actual complete chunk
   step from initial arrays/frames and its length/tag invariant, including
   payload/skip execution and pointer/length/halving updates (fresh kernel
   `83151`). `jet_buffer_write_choices.v` derives that invariant from canonical
   chunk capacities and the remaining present-byte length (fresh kernel
   `63017`, all three facts closed). Together these two modules
   have 8 results / 2 definitions; no public coverage is added.
   **Complete arbitrary Buffer63 writer independently checked.**
   `jet_write_buffer8_loop_layout.v` composes every mixed step and derives its
   length/tag decisions from canonical remaining bytes; `jet_write_buffer8_layout.v`
   derives the full actual call boundary, both disabled assertion loops, initial
   shift and return. Arbitrary padding, earlier output, crossings, unrelated
   memory and writable continuation are retained. Both modules / 3 results /
   1 definition pass source, scans, assumptions and fresh kernels `99205`, `6681`.
   The seven new writer-support modules total 21 results / 4 definitions and
   passed expanded audit `30018` (381 modules / 1745 results), against accepted
   `9cc50d6`, with terminal exit 0. All gates, negative fixtures and exact AST
   checks passed; snapshots are accepted. They add no public coverage.
   **General context writer independently checked.**
   `jet_write_sha256_context_{exec,layout}.v` derives the full actual helper
   from initial canonical buffer/state arrays and context fields. Arbitrary
   counters and both overflow returns are covered; all intermediate calls and
   reloads are discharged. Its output is the exact typed 830-cell encoding of
   buffer, represented compression count and state. The counter/buffer
   remainder condition is an initial representation invariant; public
   consumers must derive it from actual context construction. Two unregistered
   modules / 5 results pass source, scans, assumptions and fresh kernel `86693`
   (including both modules); the two shared uint32 encoding bridges are closed.
   **Next bounded SHA milestone:** compose read_sha256_context's actual buffer,
   count and state reads, private len allocation/free, counter/overflow stores
   and all overflow return cases. Derive the initialized readonly max-counter
   global observation and its preservation rather than assuming its desired
   loaded value as an unexplained public execution premise.
   **Readonly provenance and reader suffixes independently checked.**
   `jet_readonly_int64.v` and `jet_sha256_max_counter.v` derive the actual
   initialized global and its preservation through allocation, stores and
   private frees. Together with the general context writer they are registered
   for audit `58720` (385 modules / 1761 results), against `dd2b9d7`;
   all gates, negative fixtures and exact AST regeneration passed with terminal
   exit 0; filtered snapshots reproduce the baseline and are accepted.
   The unregistered `jet_read_sha256_{counter,overflow}.v` modules derive actual
   counter reconstruction and overflow store/reload/both returns from current
   memory observations and writable fields (fresh kernels `43218`, `84510`).
   Exact AST selectors connect both fragments to the generated function. Their
   initial-memory consumers do not establish whole-reader entry/calls/cleanup
   or canonical public equivalence. Compose those next; preserve readonly
   provenance explicitly, since forward permission preservation alone does
   not imply the absence of newly Writable permissions.
   Those fragments now offer observation-only consumers, preserving the
   stronger original provenance wrappers, so exact global loads can be carried
   by the existing framing interfaces. `jet_sha256_read_local.v` derives actual
   private allocation, entry, Freeable/writable permissions, separation and
   cleanup (fresh kernel `31575`). `jet_read_sha256_context_exec.v` composes the
   full actual body and function boundary (fresh kernel `72171`), but its
   intermediate call/load/store premises are INTERNAL obligations. The four
   unregistered reader modules have 25 results / 9 definitions. Next derive
   those premises from initial 830-cell frames using the complete buffer/count/
   state readers and memory framing; then prove literal canonical public specs.
   **Complete context reader independently checked.**
   `jet_read_sha256_prefix_layout.v` derives actual buffer/count reads and counter
   store from initial canonical cells (fresh kernel `13483`).
   `jet_read_sha256_context_{layout,initial}.v` derives the remaining state read,
   both overflow returns and cleanup; its initial wrapper derives the actual
   private allocation and separation rather than assuming intermediate calls or
   memory effects (fresh kernel `2334`, current layout dependency included).
   Actual arrays, counter/overflow fields, output pointer, cursor +830, global
   load, permissions and unrelated-memory framing are retained. The seven
   unregistered reader modules total 30 results / 9 definitions, with no public
   coverage added. Integrate them separately, then prove the canonical context
   representation/failure bridge and public caller equivalences. Compression
   dispatch initialization/linking is still a separate obligation on those paths.
   Its compression-count threshold is 2^55; invalid input is a required failure
   case, not an assumption to remove from a public contract. The frame.c prose
   saying 838 output cells is stale: the actual canonical context has 830.
   Context add/finalize and tapdata_init also require actual SHA compression:
   the current jets AST's mutable compression-function-pointer global has an
   empty initializer, so it does not establish a particular implementation's
   code or initialized dispatch. Resolve concrete Clight linking/initialization
   and artifact provenance before claiming any compression call. An assumed
   compression execution or functional SHA result is not public C coverage.

## Verification and completion discipline

Public results must quantify over valid non-wrapping layouts and cursors,
arbitrary unrelated output bits, and the required environments. Derive helper
execution, cursor changes and allocation/copy/store/free obligations from the
initial state. Preserve permitted memory framing. The context layer is reusable
but whole-evaluator linking is not required by this individual-jet goal.

Add modules to both project manifests, public results to the theorem audit,
and specifications/selectors/contracts to the definition snapshot. Review
assumption and contract changes before accepting updated expectations. New
proofs must preserve previous theorem types and axiom sets. Build consumers
after dependency edits: a stale `.vo` is not evidence about changed source.

The constant extension exposed a negative-test fixture bug: mutating
`jet_guarantees.v` requires rebuilding its consumers before comparing contracts.
The harness now does so; the impossible-premise test must fail because the
contract changed, not because Coq rejected an inconsistent artifact digest.
The complement extension also exposed pretty-print wrapping of long `Locate`
names in the assumption audit. The gate now uses explicit theorem-name markers
and checks missing results before either comparison or snapshot update. It does
not expand the inherited axiom allowlist.

Completion requires inspecting the full inventory, actual theorem statements,
source/Clight correspondence, supported configurations and checked assumptions.
Do not mark the goal complete based only on the subset currently in the public
build or on the coverage metadata alone.
