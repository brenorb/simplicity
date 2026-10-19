# Proposal: unblocking repository-wide acceptance at the frozen Bitcoin target

Status: proposal only. No target, theorem, gate or registry was edited for it.
Investigated 2026-10-19 on `codex/fe-multiply-integration` after merging
`feat/jet-equivalence` `2472cb0c`.

`check-jets.sh --update-expected` / `--accept` cannot pass at the pinned
original target (`91d89bac` for `C`, `Haskell`, `Coq/Simplicity`). Three
blockers were found; one is already repaired upstream.

## 1. `jet_bitcoin_count_bridge.v` — fixed upstream

Commit `7f2d7382` ("restore Bitcoin count proofs against the frozen output
bound", evidence `proof-work/bitcoin-count-frozen/`) changes one proof step to
the frozen strict bound `0 < Zlength sigTxOut`. Statements unchanged. After the
merge the file compiles here. The registered `simplicity_bitcoin_num_inputs` and
`simplicity_bitcoin_num_outputs` entries (via `jet_bitcoin_count_local`) depend
on it. No action needed.

## 2. `jet_bitcoin_value_domain.v` — open; proposed: retire three lemmas

Failure: `Definition domain_input` cannot build a `sigTxInput` without the
frozen `sigTxiValue_bound : moneyRange (Int64.signed sigTxiValue)` field. The
module was written for the former altered model.

Content (7 public theorems; no `.v` file imports it; no coverage entry depends
on it):

| Lemma | Frozen-model status |
| --- | --- |
| `word64_eqm`, `signed_unsigned_sum_eqm`, `bitcoin_total_input_unsigned`, `bitcoin_total_output_unsigned` | domain-independent; compile against the frozen model and are closed (checked on a scratch copy truncated before `domain_input`) |
| `bitcoin_positive_fee_representable`, `bitcoin_empty_outputs_representable`, `bitcoin_high_bit_value_representable` (+ `domain_*` witnesses) | assert representability of environments the frozen model excludes (positive fee, empty outputs, bit-63 values); `proof-work/original-target-boundary/` proves the frozen domain excludes exactly these |

Options (each needs approval; all leave the target untouched):

* **A1 (recommended).** Delete the three representability lemmas and the
  `domain_*` definitions from `jet_bitcoin_value_domain.v`, keeping the four
  general lemmas with unchanged statements. Remove their 3 records from
  `jet_public_theorems.txt` (and any contract definitions). Optionally add the
  `original-target-boundary` exclusion facts as a separate module, stating the
  restriction instead of the impossible representability. Coverage impact: none.
  Snapshot impact: 3 assumption/contract records removed, none changed.
* **A2.** Retire the whole module from both projects and the public list
  (7 records removed). Simpler, but it drops four correct lemmas.

Not proposed: changing the frozen `Coq/Simplicity/Primitive/Bitcoin.v` domain.

## 3. Bitcoin primitive identity gate — open; needs an explicit target decision

`check-bitcoin-primitive-identity.py` fails with `Bitcoin base primitive name
mismatch: LockTime`. The frozen Coq model has `LockTime => "locktime"`
(`Coq/Simplicity/Primitive/Bitcoin.v:108`); the canonical Haskell has
`primName LockTime = "lockTime"` (`Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs:69`).
Both are byte-identical to `91d89bac`, so this is an upstream discrepancy, not a
local edit. `proof-work/bitcoin-frozen-identity/` proves (closed, kernel-checked)
that the two resulting primitive tags differ. This affects primitive identity
(commitment tags), not the C value computed by the lock-time jet.

Options:

* **B1. Report upstream and wait (recommended first step).** File the
  `locktime`/`lockTime` discrepancy with BlockstreamResearch/Simplicity,
  attaching the closed inequality proof. Acceptance stays blocked until upstream
  resolves it, or until B2 or B3 is chosen.
* **B2. Documented target deviation.** Correct the Coq frozen name to
  `"lockTime"` as an explicit, recorded exception to the 91d89bac guard
  (guard and source-target pin updated to list exactly this one-line
  deviation). Every identity-dependent Bitcoin proof then needs a fresh rebuild
  and review. Changes a frozen specification, so it needs explicit approval.
* **B3. Scoped gate exception.** Keep the frozen model and make the identity
  gate list this one mismatch as a known, proved upstream discrepancy (keyed to
  the `bitcoin-frozen-identity` theorem), still failing on any other mismatch.
  This weakens a gate, so it needs explicit approval; identity-dependent Bitcoin
  coverage would have to be labelled as relative to the frozen Coq identity.

## Effect on the field jets

Neither blocker touches the field proofs. Their closures load no Bitcoin
primitive module (also noted in `proof-work/secp-field-acceptance/`).
