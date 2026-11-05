# Funded Sablier cliff stream

`app-sablier-cancelable-cliff-stream` implements one native BTC stream with a
fixed cliff schedule, a sender, two possible recipients, and a cancellation
valuation authority. The lifecycle includes funding, partial withdrawals,
recipient transfers, irreversible cancellation, and depletion. The Integer
reference and Simplicity program are independent implementations.

All 38 native vectors passed with one canonical CMR
`90d8d7cbb938b11a6768d2e0193657960b7a02d848cd7709c8a403ef36df083a`.
The 13 positive fixtures passed the independent wire, actual C/Haskell
primitive and ancestry checks. The arithmetic agreed at all 59 tested heights.

The pinned Sablier release is `18fce3d1cad30f1e641fe9eff3a913ee5cdd54ae`.
`calculateStreamedAmountLL` gives the schedule arithmetic. `_create`, `_update`,
`_streamedAmountOf`, `_cancel` and `_withdraw` give the funding, transfer and
credit rules. The source inventory records the hashes of all nine retained
Sablier files and licenses. The source files carry BUSL-1.1 and are retained as
inert inputs for this research corpus.
[LockupMath.sol](https://github.com/sablier-labs/evm-monorepo/blob/18fce3d1cad30f1e641fe9eff3a913ee5cdd54ae/lockup/src/libraries/LockupMath.sol)
[SablierLockup.sol](https://github.com/sablier-labs/evm-monorepo/blob/18fce3d1cad30f1e641fe9eff3a913ee5cdd54ae/lockup/src/SablierLockup.sol)

| Schedule field | Fixed profile |
| --- | ---: |
| Deposit | 37,111 sats |
| Start height and unlock | 800,000 and 2,500 sats |
| Cliff height and unlock | 800,011 and 4,600 sats |
| End height | 800,050 |
| Granularity | 7 blocks |
| Linear portion and duration | 30,011 sats and 39 blocks |

Vesting is zero before start and equals the start unlock before the cliff. At
and after the cliff, through the block before end, it equals
`7100 + floor(floor((height - 800011) / 7) * 30011 * 7 / 39)`.
At end it equals the full deposit. The Simplicity expression computes both
floor divisions on the actual chosen height. It uses the bounded product
`steps * 210077`, which fits in a 64-bit word. The cliff step uses elapsed time
since cliff, and the final block rule releases the remainder at end even
though granularity does not divide the duration.

Input 0 spends the state UTXO. Its committed phase, owner, last valued height,
withdrawn balance and refunded balance are opened by one typed witness. The
program checks the current index, input count, distinct outpoints, internal
key and empty Taproot path. It compares the actual spent script against the
complete state commitment and actual executable leaf, then checks actual value
against the calculated remaining balance and the separate 10,000-sat carrier.
The pending carrier UTXO starts the profile. A sender-authorized funding
transaction consumes a distinct sender-script input of 38,111 sats and places
47,111 sats under the funded state. Later transitions require a separate
1,000-sat fee input. Ordinary Bitcoin validation authorizes that additional
input and enforces transaction finality and coin existence.

The program derives the entire next state and ordered output plan. Live
withdrawals use the enabled `nLockTime` height as a conservative valuation
and advance the committed height. Transfers change only the recipient key.
Cancellation requires the sender and a separate BIP340 signature from the
valuation authority on the tagged digest of the actual `sig_all_hash` followed
by the explicit 32-bit height. The event binds the current outpoint, input
values and scripts, sequences, outputs, locktime, executable leaf and current
index through that signature hash. Its height must equal enabled `nLockTime`
and be at least the last committed valuation. The authority is trusted to
attest the valuation at signing. A signed transaction can confirm later, and
the chain enforces the lower height bound. The event has no on-chain expiry.

The source formulas give `refund = deposit - vested` and
`retained credit = vested - withdrawn`. Cancellation pays the original sender,
persists the refund and leaves the retained credit to the current recipient.
Later claims and transfers preserve the canceled phase and refunded amount.
The frozen entitlement is `deposit - refunded` regardless of later height.
Every continuation carries exactly `deposit - withdrawn - refunded` plus the
carrier under the same executable leaf. The recipient receives the full final
credit at depletion, and the sender recovers the carrier in a separate output.
When cancellation leaves zero credit, the sender receives the refund and carrier
in a single terminal output. This profile uses native keys and outputs for the
foreign ERC721 ownership and ERC20 escrow roles.

| Linked positive sequence | State output, sats | Payout output, sats |
| --- | ---: | --- |
| Fund | 47,111 | |
| Start claim | 45,611 | 1,500 to recipient 0 |
| Last pre-cliff claim | 44,611 | 1,000 to recipient 0 |
| Transfer live right | 44,611 | |
| Cliff claim | 42,611 | 2,000 to recipient 1 |
| First granularity step claim | 39,611 | 3,000 to recipient 1 |
| Cancel at 800,026 | 20,373 | 19,238 to sender |
| Transfer frozen right | 20,373 | |
| Frozen partial claim | 18,373 | 2,000 to recipient 0 |
| Frozen depletion | | 8,373 to recipient 0 and 10,000 to sender |

The alternative paths test live depletion at end, cancellation before start,
and cancellation once earlier claims consumed all vested credit. The adversarial
fixtures vary funding amounts and scripts, signing roles, enabled locktime,
vesting boundaries, stale and replayed valuations, terminal or duplicate
cancellation, actual input indexing, state openings, continuation credit, and
recipient and sender destinations. For transaction mutations, signatures are
regenerated over the changed transaction except where a replay is intentional.

Build the test executable from `jet-discovery/` with GHC 9.8.4 and the cached
package database, then launch the bounded vector cohort.

```sh
ghc -O1 -w -threaded -rtsopts -isrc \
  -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery \
  -outputdir /private/tmp/sablier-stream-build tools/SablierStreamSmoke.hs \
  -o /private/tmp/sablier-stream-smoke
python3 tools/run_sablier_stream_vectors.py
```

The diagnostic driver uses `-O0` to avoid expanding the wide C/Haskell value
comparisons in the GHC optimizer. The stream kernel is built at `-O1`.
The exact fixture set, Integer model, source hashes and run log accompany
the diagnostic. The initial state carrier and separate fee inputs are
synthetic test coins. Successor outpoints use the actual txids of the
preceding fixtures.
The driver checks the arithmetic at every height in the fixed schedule and
its immediate boundaries. It checks actual raw outpoints, amounts and scripts
through both the C and Haskell primitives for every accepted fixture, and
checks that each successor input opens the previous transaction's actual
output 0 with the correct amount and script.

The full run exited 0 in 190.839 seconds of RTS elapsed time at
`-N1 -A16m -M8G -s`. Its maximum live residency was 2,191,947,712 bytes and
total RTS memory was 5,724 MiB. The log and provenance are
`reports/data/sablier-stream-full38-8g-rts.txt` and
`reports/data/sablier-stream-full38-8g-provenance.json`. The hashes of the
unchanged compiled source closure, pinned upstream inputs, executable and
log all verified. This records vector execution. The shared corpus analysis
supplies separate cost and budget measurements.
