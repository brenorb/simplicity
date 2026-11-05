# Delegated snapshot governance and native treasury execution

`app-oz-delegated-snapshot-governance` governs one initialized 100,000-sat
treasury with three fixed accounts and one proposal. Voting units can move
between accounts and be delegated independently of treasury value. The
proposal chooses one of two fixed P2TR destinations and commits an exact
payment between 2,000 and 50,000 sats.

All 63 native vectors passed with one canonical CMR
`911ac4893600b4c83fd0bd3ac2035e2692ad3d67e7ceb997998bc2abf4e15e9d`.
The run covered 30 accepted and 33 rejected transitions. All 12 quorum
comparisons and all 30 linked wire and primitive checks passed.

The independent Integer model follows the OpenZeppelin sources pinned at
`efaa6f78ab1dde05416246e801c0baaf4f900d49`. `Votes` tracks voting units by their
direct delegate and includes undelegated units in total supply. `Checkpoints`
returns the latest weight at or before the requested past timepoint.
`GovernorVotes` reads that past weight. `GovernorCountingSimple` counts the
three ballot types once per account and requires for plus abstain for quorum,
with strictly more for than against. `GovernorVotesQuorumFraction` floors
the fraction of the past total supply. The pinned six source files and MIT
license were retained as inert data and verified against their audit hashes.
[Governor](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/efaa6f78ab1dde05416246e801c0baaf4f900d49/contracts/governance/Governor.sol)
[Votes](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/efaa6f78ab1dde05416246e801c0baaf4f900d49/contracts/governance/utils/Votes.sol)
[Checkpoints](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/efaa6f78ab1dde05416246e801c0baaf4f900d49/contracts/utils/structs/Checkpoints.sol)
[GovernorVotes](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/efaa6f78ab1dde05416246e801c0baaf4f900d49/contracts/governance/extensions/GovernorVotes.sol)
[GovernorCountingSimple](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/efaa6f78ab1dde05416246e801c0baaf4f900d49/contracts/governance/extensions/GovernorCountingSimple.sol)
[GovernorVotesQuorumFraction](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/efaa6f78ab1dde05416246e801c0baaf4f900d49/contracts/governance/extensions/GovernorVotesQuorumFraction.sol)

The setup fixes 301 voting units, balances 101/100/100, and initial
self-delegation. The delegate value 3 denotes an undelegated balance. A
transfer debits one account and credits another. A delegation moves the
current voting power of the account's own units. The proposal transition
derives its three snapshot weights from the actual opened balances and
delegates at the prior committed clock value. This is the only historical
checkpoint the single proposal can query. Later state changes preserve it.
Every ballot reads the stored weight and sets its account's one-use bit.
The state checks total supply, delegate indices, all three snapshot weights,
bitmap range and agreement between recorded ballot weight and tally sum.

The native quorum is `floor(301 * 40 / 100) = 120`. Keeping supply fixed
means the actual sum of committed balances equals past total supply even
after transfers and delegation changes. The native expression multiplies
that sum by 40, divides by 100 with integer flooring, and tests for plus
abstain against it. Approval also requires `for > against`.

The native clock starts at event 1. Creation captures the prior ledger at
event `s`, and its successor admits voting at events `s+1` through `s+6`,
inclusive. Each accepted transfer, delegation or ballot uses one slot.
Anyone can advance one slot through a state-preserving CSV1 tick. Queue or
refund becomes available at `s+7`. Queue carries the successful proposal
under the same leaf, and execution then requires CSV2 on the queued output.
This makes elapsed voting time depend on transaction inclusion and the mix
of events. Signed events can fill slots faster than six blocks. Public ticks
need successive blocks and fee funding, so passage of time alone leaves an
idle proposal open. Proposal creation uses a zero threshold and the clock
is bounded before proposal creation to fit the committed 16-bit fields.

The one aggregate witness opens the old ledger and supplies the action and
its authorization. Signed actions verify BIP340 over a tagged digest of the
actual `sig_all_hash` followed by `mode8 || actorBE16 || selectionBE16 ||
quantityBE16`. This commits the ballot's exact support even when its weight
is zero and all three choices would produce the same tally and transaction.
The program derives the entire successor ledger and treasury plan.

Current input 0 must match the opened state's actual Taproot script and
100,000-sat value. The program checks the internal key, empty path, distinct
outpoints and exact two-input count. Input 1 independently supplies 1,000
sats for fees. Each continuation preserves the exact treasury value under
the same executable leaf. Successful execution pays the committed target
and amount plus the exact treasury remainder to the recovery key. Failure
pays the whole treasury to that key. Both are terminal and constrain every
output script, value and count. Bitcoin input validation supplies existence,
age and authorization for the fee input. This native profile covers a
single treasury proposal with a fixed payout action and fixed parameters.

| Completed fixture branch | Snapshot weights | Against / for / abstain | Result |
| --- | --- | --- | --- |
| Exact quorum after post-snapshot changes | 70 / 50 / 0 | 0 / 70 / 50 | 25,001 sats to target 0 and 74,999 returned |
| Alternate successful proposal | 101 / 100 / 100 | 0 / 200 / 101 | 42,001 sats to target 1 and 57,999 returned |
| Tie despite quorum | 101 / 100 / 100 | 100 / 100 / 101 | Full 100,000-sat refund |
| Majority without quorum | 70 / 50 / 0 | 0 / 70 / 0 | Full 100,000-sat refund |

In the first branch, transfers and delegation change the current power to
120/0/0 after the snapshot. The first two accounts still vote with 70 and
50 respectively, and the zero-weight third account uses its own ballot bit
on the final active slot. The negatives try to substitute the current power,
forge old or new checkpoint fields, vote twice, relabel a signed zero-weight
ballot, queue before expiry or after defeat, execute before CSV2, change the
committed payment, divert the treasury, or replay execution on its remainder.
Authorized negative transactions are signed again except the deliberate
same-transaction ballot relabeling.

The initial treasury and fee inputs are synthetic test coins. Successor
outpoints use the raw txids of the actual preceding fixtures. The driver
checks their serialized transactions, state ancestry, 1,000-sat fee
conservation and both actual C and Haskell primitive views. It also compares
the native quorum expression to the Integer model across 12 input supplies.

Build and run the bounded diagnostic from `jet-discovery/` with GHC 9.8.4.

```sh
ghc -O1 -w -threaded -rtsopts -isrc \
  -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery \
  -outputdir /private/tmp/snapshot-governor-build tools/SnapshotGovernorSmoke.hs \
  -o /private/tmp/snapshot-governor-smoke
python3 tools/run_snapshot_governor_vectors.py
```

The diagnostic driver uses `-O0` for the wide C/Haskell value comparisons.
The kernel uses `-O1`. The run records hashes of the exact source closure,
pinned primary inputs, executable and log.

The run exited 0 with 102.842 seconds of RTS elapsed time at
`-N1 -A16m -M8G -s`. Maximum live residency was 1,339,716,864 bytes and total
RTS memory was 3,608 MiB. The source closure, primary inputs, executable and
log hashes verified. Exact results are retained in
`reports/data/snapshot-governor-full63-8g-rts.txt` and
`reports/data/snapshot-governor-full63-8g-provenance.json`. The shared corpus
runner supplies separate cost and budget measurements.
