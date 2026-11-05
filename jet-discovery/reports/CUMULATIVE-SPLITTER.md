# Native cumulative pull-payment splitter

`app-cumulative-payment-splitter` passes **all 28 native vectors** under one
canonical CMR, `a8f8241e786a083bb5c759a6fbd0d2a11f73a8b1d835ed42eae3658ace70fc92`.
It is a full bounded native state machine for the Ether branch of OpenZeppelin
[PaymentSplitter v4.9.6](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/finance/PaymentSplitter.sol).
The source and its MIT license are inert data in
[`vendor-specs/contract-extras`](../vendor-specs/contract-extras/provenance.json).

The source computes the lifetime receipts as current balance plus total
released, then pays `floor(lifetime receipts × shares / total shares)` less
what that payee already received. This is a history-dependent pull payment:
each of six separate 1-sat deposits floors to zero for the 1/6 payee when
considered alone, but their cumulative entitlement is 1 sat. Withdrawal by a
different payee must not reduce that entitlement. An independent Integer
reference uses the source formula and checks all six release orders.

| Transition | Current state and actual funding | Output requirements |
| --- | --- | --- |
| Receive | Current input 0 is the actual committed state UTXO. One other input funds a positive increment plus a fixed 1,200 sat fee. | Exactly one successor with the same executable leaf, higher lifetime receipts, all release counters unchanged and increased backing. |
| Release | Current input 0 is the committed state UTXO. The other input funds exactly the fee. Any caller can request an outstanding share. | Exact recipient script and positive newly accrued amount; exactly one successor with lower backing, unchanged receipts, and only that payee's counter advanced. |

One typed witness opens the receipt total, all three release counters and the
action. The program checks each released counter against the exact rounded
entitlement and derives the new ledger, without a second alleged state. It
binds the current script and value, the state-derived Taproot commitment, the
successor's script and value, and the exact count and scripts of all outputs.
Receipt history is bounded to 48 bits with checked additions/subtractions.
The 1:2:3 share configuration is immutable. A separately funded 1,000 sat
anchor remains in the state UTXO even when all payees have collected, so the
splitter can receive again. It never increases entitlement. Funding the first
anchor and signing the external fee input are setup/transaction responsibilities.
There is no ERC20, reconfiguration, arbitrary payee list or EVM callback claim.

The 14 accepting and 14 rejecting fixtures cover lifetime rounding, actual
predecessor outputs, both claim orders, repeat deposit after complete release,
ordinary-sized payout, receipt limit, false history, missing funding, wrong
recipient, inflated payout, wrong continuation/current script or value, fee
underflow, and re-release with nothing owed. Two genuine identical state UTXOs
at different indices share the same payout in an isolated input-evaluation
control: the same vector context accepts index 0 and rejects index 1. It is not
a claim that the two-input transaction as a whole can spend both covenant
outputs. The one-sat vectors are exact consensus-level arithmetic fixtures
and may be relay dust. The positive 2,000 sat example is separate.

The [complete log](data/cumulative-splitter-full28-4g.txt) and
[run record](data/cumulative-splitter-full28-4g.json) record actual exit 0,
104.677 seconds elapsed and 1,674,713,696 bytes maximum live residency
(`-N1 -A16m -M4G`). Every vector checks the canonical program commitment and
uses prepared evaluation. Runtime is validation evidence; shared static costs
are still pending the whole-corpus run. Recompile `tools/CumulativeSplitterProbe.hs`
with the local package database and flags in [CRYPTO-FAMILIES.md](CRYPTO-FAMILIES.md),
then run it with the recorded RTS flags. No downloaded code is executed.
