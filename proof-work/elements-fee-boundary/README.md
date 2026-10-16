# Fee-jet fidelity obligation discovered during ordering review

`output_is_fee` is not just another scalar getter. Before attempting its final
implementation-to-specification theorem, resolve this exact source boundary:

- `C/elements/env.c`, `copyOutput`: `result->emptyScript = 0 == output->scriptPubKey.len`.
- `C/elements/elementsJets.c`, `isFee`: the cached `emptyScript` flag and both
  explicit asset/amount prefix tests.
- `Haskell/Simplicity/Elements/Programs/Transaction.hs`, `outputIsFee`: the
  amount/asset pair, **OutputScriptHash equality with `Right emptyHash`**, and
  the explicit asset/amount cases.
- The Haskell primitive computes the script hash from `txoScript`; it does not
  directly expose script length. The C builder's flag therefore cannot simply
  be represented by that hash-equality test without an additional proof.

The empty-script-to-empty-hash direction follows by computation. For an
arbitrary nonempty script, the converse requires excluding another preimage
of the empty-script hash, or a different justified restriction on the actual
accepted script domain. Neither generic hash injectivity nor this particular
preimage exclusion has been proved here. No concrete collision or differing
valid transaction is exhibited by this inspection, so this is **a proof/fidelity
obligation, not a demonstrated executable counterexample or confirmed bug**.

Do not silently define `emptyScript` to mean hash equality, assume hash
injectivity, add an execution/output premise, or register a theorem for an
easier specification. A C-level `isFee` execution lemma is still useful, but
does not discharge the canonical bridge. Any genuinely conditional result must
be distinguished from unconditional equivalence and its premise checked
against real callers. The same issue propagates to the canonical `totalFee`
program, which uses `outputIsFee`.

The existing `Coq/elements-env/C/jet_elements_env_isfee.v` concerns env.c's
**rawElementsOutput** helper, not the jet unit's **sigOutput** helper. Its AST,
field offsets and statement are different; do not apply it by name alone.

No accepted sources, registries, assumptions or C implementations were changed
for this note. Continue with non-cryptographic issuance token-amount routing
or other unaffected missing jets while investigating this obligation.
