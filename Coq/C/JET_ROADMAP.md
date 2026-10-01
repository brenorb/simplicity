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

There are 22 covered core jets: one/increment/add at 8/16/32/64 bits and
low/high at 1/8/16/32/64 bits. There are 511 declarations without coverage
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
2. **Simple bitwise jets next.** Start with complement at 8 bits, then 16/32/64,
   reusing the total readers and writers, input encoding, frame lifecycle and
   canonical context results. Prove a reusable bitwise representation bridge
   rather than exhaustively enumerating larger words. Single-bit variants need
   a total arbitrary-layout bit-reader contract; do not replace it with a
   fixed-cursor experiment and count that as complete coverage. Then binary
   and ternary operations, predicates and simple comparisons.
3. **Arithmetic families.** Subtraction/decrement and carry-input variants
   should reuse the increment/add machine-value, carry and word-modulo facts.
   Keep width-independent arithmetic separate from generated-body adapters.
   Afterwards tackle shifts/rotates, multiplication, division and larger widths.
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

Completion requires inspecting the full inventory, actual theorem statements,
source/Clight correspondence, supported configurations and checked assumptions.
Do not mark the goal complete based only on the subset currently in the public
build or on the coverage metadata alone.
