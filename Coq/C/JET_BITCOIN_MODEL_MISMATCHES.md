# Reported mismatches: frozen Coq Bitcoin model vs canonical Haskell

Original report: 2026-10-19, against the unchanged `91d89bac` model.
Current update: 2026-11-23, authorized local fee-only correction in M2.

**Policy and current status.** Unrelated mismatches remain reported and frozen.
On 2026-11-23 the user explicitly authorized correcting M2 and its proof,
representation and acceptance consequences. The current local model defines
fee as input minus output, retaining every monetary/structural bound and the
M1 name. Original upstream provenance and the local correction are distinct;
see [the repair scope and validation](JET_BITCOIN_FEE_REPAIR.md).

Each entry gives the two sources, the kernel-checked evidence, and the effect on
the jet proofs. Uncorrected entries remain discrepancy reports; M2 records the
specifically authorized local correction.

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

**Gate:** `Coq/check-bitcoin-primitive-identity.py` compares the frozen base file
with Haskell. It fails on any difference not documented by a marker below, and
on a documented one that has disappeared. It prints the documented ones on every run.

<!-- gate bitcoin-base name LockTime "locktime" "lockTime" -->

## M2. Fee definition and its bound — locally corrected

| Source | Definition |
| --- | --- |
| Original upstream Coq `Bitcoin.v:54,57` | `sigTxFee := sigTxTotalOutValue - sigTxTotalInValue`, with `moneyRange sigTxFee` |
| Corrected local Coq `Bitcoin.v:54,57` | `sigTxFee := sigTxTotalInValue - sigTxTotalOutValue`, retaining `moneyRange sigTxFee` |
| Unchanged Haskell `DataTypes.hs:166-167` | `txFee tx = txTotalInputValue tx - txTotalOutputValue tx` (no type-level bound) |
| Unchanged C `bitcoinJets.c` | `totalInputValue - totalOutputValue` written as Word64 |

The reversed definition originates in upstream commit
`6e0ddfbbbc55903833b7cdc30790b0a2269505fb` (2018-05-01), before local
proof work. Together with `moneyRange` it excluded inputs 10 / outputs 9.
`original_bitcoin_excludes_ten_in_nine_out` is evidence about that original
source, retained in the historical boundary diagnostic; it is not a theorem
about the corrected model.

The local change is exactly the operand order. The lower bound now expresses
nonnegative fees on ordinary non-creating transactions. Its upper bound is
redundant given the unchanged money-range totals and `outputs <= inputs`.
`bitcoin_fee_admissible` and `bitcoin_tx_from_lists` establish this for arbitrary
input/output lists under all remaining validity conditions. Coinbase, arbitrary
raw Word64 aggregates, empty outputs and high-bit amounts are not newly admitted.

The registered `bitcoin_fee_local_spec` already proves actual C execution of
the literal input-minus-output program. Its type and proof remain intact.
`jet_bitcoin_fee_domain.v` connects every corrected environment to that theorem
using a constructed exact-total representation and complete encoded-frame,
separation, success-return, output and memory-framing witness. It also proves
exact integer decoding without modular wrap, and includes 10/9/1 and 10/10/0
instances and canonical raw/extended hashing projections. These new results
are registered for normal contract/assumption checks; their validation status
is recorded in the repair report.

Only the `Bitcoin.v` content pin and the manifest's two enforcing digest pins
change. All 282 other frozen inputs retain their original hashes. Historical
build results apply only to their recorded sources; they do not validate this
correction.

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
> 2. originally defined `sigTxFee` as total output minus total input and requires it to be in
>    money range, while Haskell's `txFee` is total input minus total output.
>    As a result, the record cannot represent a transaction whose inputs exceed its
>    outputs (locally corrected on 2026-11-23; see M2);
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
- the identity gate's base-model comparison (`33d1ac06`), which expected the edited
  model, is replaced by a report-driven one: any undocumented difference fails,
  and documented ones are printed;
- registry entries for the removed lemmas are dropped. The contract and
  assumption snapshots are regenerated by `check-jets.sh --update-expected`;
- the review notes now point here.
