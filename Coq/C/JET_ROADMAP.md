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

There are 75 covered core jets: one/increment/add/full_increment at 8/16/32/64 bits,
low/high/complement/and/or/xor/maj/xor_xor/ch/some at 1/8/16/32/64 bits,
all at 8/16/32/64 bits, and eq at 1/8/16/32/64 bits.
There are 458 declarations without coverage
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
   unbounded sum; reuse its existing wraparound bridge. Next add full_add using
   a carry-bit read followed by the two existing word reads. Its generated carry
   is a short-circuit conditional assigning `_t'4`, not a single expression.
   Execute that branch explicitly before composing the carry and word writers.
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
