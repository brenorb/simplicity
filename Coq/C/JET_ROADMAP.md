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

There are 127 covered core jets: one/increment/add/full_increment/full_add/subtract/negate/decrement/full_decrement/full_subtract/lt/le/is_zero/is_one/min/max/median at 8/16/32/64 bits,
low/high/complement/and/or/xor/maj/xor_xor/ch/some at 1/8/16/32/64 bits,
all at 8/16/32/64 bits, and eq at 1/8/16/32/64 bits.
There are 406 declarations without coverage
entries, including all Bitcoin and Elements jets. Coverage is for the pinned
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
4. **Failure-capable jets.** Extend the current success-only `jet_local_spec`
   infrastructure with a contract tied to the Simplicity assertion semantics,
   covering both return values and the permitted memory effects on failure.
   The inventory's theorem-shape validation must be extended explicitly for
   that contract. Do not force partial specifications into a total function or
   assume away failures merely to reuse the current predicate.
5. **Hashing, secp256k1 and application primitives.** Reuse the library and
   existing cryptographic verification lemmas where they actually apply.
   `Simplicity/SHA256.v:hashBlock_correct` connects a Simplicity term to VST's
   functional SHA model, not the full generated C jet call; it is support for
   a future C-to-Simplicity proof, not an additional covered jet. Likewise,
   committed `jets_secp256k1.v` avoids one AST-generation step but does not
   itself establish jet equivalence. Check artifact provenance and configuration
   before using it. Bitcoin/Elements require concrete environment representations,
   their primitive semantics, failures and suitable generated C artifacts.

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
