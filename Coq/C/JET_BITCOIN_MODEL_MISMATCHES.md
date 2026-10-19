# Reported mismatches: frozen Coq Bitcoin model vs canonical Haskell

Date: 2026-10-19. Target pinned at `91d89bac` (`C`, `Haskell`, `Coq/Simplicity`
unchanged).

**Policy.** Mismatches between upstream sources are **reported, not corrected**.
They may be evidence of upstream bugs, and the Simplicity developers are the
ones to evaluate them. The frozen files stay byte-identical. Proofs are stated
against the frozen model as it is. Their scope is recorded here, so that a
mismatch never quietly changes what a theorem means.

Each entry gives the two sources, the kernel-checked evidence, and the effect on
the jet proofs. The entries do not judge which side is right.

## M1. `LockTime` primitive name

| Source | Text |
| --- | --- |
| Coq `Coq/Simplicity/Primitive/Bitcoin.v:108` | `\| LockTime => "locktime"` |
| Haskell `Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs:69` | `primName LockTime = "lockTime"` |

**Evidence:** `original_bitcoin_locktime_name` and
`original_bitcoin_locktime_name_not_canonical_case`, closed theorems in
`proof-work/original-target-boundary/source/OriginalDomainBoundary.v.source`.
The name feeds the primitive's commitment tag, so the two tags differ.

**Effect on the jet proofs:** no C jet reads the name. `simplicity_bitcoin_lock_time`
is proved about the C function's returned value. No registered theorem claims
that the Coq and Haskell commitment identities are equal.

**Gate:** `Coq/check-bitcoin-primitive-identity.py` is back to its 2026-10-04
form. It compares our extended primitive interface (`C/jet_bitcoin_ext_prim.v`)
with Haskell and does not inspect the frozen base file, so this mismatch is
recorded only in this report.

## M2. Fee definition and its bound

| Source | Definition |
| --- | --- |
| Coq `Bitcoin.v:54,57` | `sigTxFee := sigTxTotalOutValue - sigTxTotalInValue`, with record field `sigTxFee_bound : moneyRange sigTxFee` |
| Haskell `DataTypes.hs:166-167` | `txFee tx = txTotalInputValue tx - txTotalOutputValue tx` (no bound) |

**Observation:** the two definitions subtract in opposite orders. Together with
`moneyRange` (`-1 < x < MAX_MONEY + 1`), the Coq record admits only
transactions whose total output is at least their total input.

**Evidence:** `original_bitcoin_excludes_ten_in_nine_out` (same file) proves that
no frozen `sigTx` has inputs 10 and outputs 9.

**Effect on the jet proofs:** the registered `simplicity_bitcoin_fee` spec is the
Simplicity program `total_input - total_output` (`jet_bitcoin_fee_spec.v`). It
does not use `sigTxFee`. All 36 registered `simplicity_bitcoin_*` proofs are
quantified over the frozen `sigTx`. So they are statements about the transactions
that model can represent. Under the observation above, that set contains no
transaction whose inputs exceed its outputs. Whether the scope should be wider
is the upstream question this report raises.

## M3. Structural bounds

| Constraint | Coq record | Haskell |
| --- | --- | --- |
| Each input or output value within money range | `sigTxiValue_bound`, `txoValue_bound` | the same check applied when parsing (`getValue`, `DataTypes.hs:84-88`), not in the type |
| At least one output | `sigTxOutBounds : 0 < Zlength sigTxOut` | `Vector`, may be empty |
| Totals within money range | `sigTxTotal{In,Out}Value_bound` | not checked (`Word64` sums) |

**Evidence:** `original_bitcoin_outputs_nonempty` and
`original_bitcoin_excludes_high_bit_input` (same file).

**Effect on the jet proofs:** the scope is limited the same way as for M2.

## Draft for the Simplicity developers (not filed)

> **Coq Bitcoin primitive model differs from the Haskell definitions**
>
> At `91d89bac`, `Coq/Simplicity/Primitive/Bitcoin.v`:
> 1. names `LockTime` `"locktime"`; Haskell's `primName LockTime` is `"lockTime"`,
>    so their primitive tags differ;
> 2. defines `sigTxFee` as total output minus total input and requires it to be in
>    money range, while Haskell's `txFee` is total input minus total output.
>    As a result, the record cannot represent a transaction whose inputs exceed its
>    outputs;
> 3. requires at least one output and money-range totals, which the Haskell types
>    do not.
>
> Closed Coq proofs of each observation are available. Are these intended?

## History: how these blocked acceptance

On 2026-10-05, commit `463a4297` (old history) **edited** the frozen `Bitcoin.v`
toward the Haskell definitions, instead of reporting the differences. It changed the name, the fee
order and the bounds, and it added files that depended on the edited model:
`jet_bitcoin_value_domain.v` examples, identity-gate expectations and review
prose. On about 2026-10-16 the history was rewritten so the target stayed pinned,
which removed the edit but kept those dependents. As a result:

- the identity gate expected `"lockTime"` in the frozen file, and `check-jets.sh`
  stopped at its static checks;
- `jet_bitcoin_value_domain.v` built example transactions that the frozen model excludes
  (positive fee, no outputs, a bit-63 amount), and it no longer compiled;
- several review notes still described the edited model.

On 2026-10-19 the frozen target was left untouched, and the work built on the
2026-10-05 edit was rewound to its state just before that edit:

- `jet_bitcoin_current_jets.v`, `_fee_local.v`, `_indexed_scalar_jets.v`,
  `_input_value_spec.v` and `_totals_local.v` are identical to `6b858b22^` again.
  `_input_value_local.v` keeps only its later, unrelated frame-range line
  (`21a16756`). `_count_bridge.v` was already back to that state (`7f2d7382`);
- `jet_bitcoin_value_domain.v`, which did not exist before 2026-10-05, is removed;
- the identity gate is the 2026-10-04 version (`35d1e347`). The base-model
  comparison and its test (`33d1ac06`), which expected the edited model, are removed;
- registry entries for the removed lemmas are dropped. The contract and
  assumption snapshots are regenerated by `check-jets.sh --update-expected`;
- the review notes now point here.
