# Funded native Maker Clipper liquidation

`app-maker-clipper-partial-liquidation` implements one initialized native
auction with kick, partial purchase, restart, yank and terminal settlement.
The model uses real BTC outputs for collateral, quote payments and surplus.
One collateral unit is 100 funded sats, and one quote unit is one bidder sat.
The remaining debt target is an accounting cap. Bidder inputs supply every
sat paid to the debt sink.

The pinned Sky DSS sources are `fa4f6630afb0624d04a003e920b0d71a00331d98`.
`clip.sol` supplies `kick`, `take`, `status`, `redo` and `yank`. `abaci.sol`
supplies `LinearDecrease`. The two sources and their AGPL-3.0-or-later license
are retained as inert inputs with verified hashes in the source inventory.
[clip.sol](https://github.com/sky-ecosystem/dss/blob/fa4f6630afb0624d04a003e920b0d71a00331d98/src/clip.sol)
[abaci.sol](https://github.com/sky-ecosystem/dss/blob/fa4f6630afb0624d04a003e920b0d71a00331d98/src/abaci.sol)

| Profile parameter | Value |
| --- | ---: |
| Starting price | `100 * RAY` |
| Linear duration, `tau` | 100 event units |
| Reset tail | 80 event units |
| Reset cusp | 40% of starting price |
| Dust target, `chost` | 1,000 quote units |
| Initial lot and debt bounds | 1 to 1,000 units and 1 to 100,000 sats |
| Separate setup carrier and spend fee | 10,000 sats and 1,000 sats |

With `RAY = 10^27`, the inner source division by 100 is exact. At elapsed
`d < 100`, `LinearDecrease` gives `(100 - d) * RAY`. At `d >= 100` it gives
zero. The native program computes the same price in whole quote units.
Raw debt and `chost` in the Integer reference are the whole quote amounts
times `RAY`. Therefore source products, capped debts and dust adjustments
are multiples of `RAY`, while the slice quotient retains the source floor.
The source reset test uses strict `elapsed > tail` or `price/top < cusp`.
In this fixed curve the cusp binds first, so the exact 40 quote is live and
39 requires reset. The reference evaluates the price at full RAY scale.

`take` starts with the smaller of requested and remaining collateral. If
its preliminary cost exceeds remaining debt, the program sets `owe = tab`
and floors `slice = owe / price`. If a partial slice would leave positive
debt below `chost`, the program requires `tab > chost`, sets
`owe = tab - chost`, then floors the slice. The adjusted `owe` survives the
floor. A full-lot sale bypasses the dust check. The native profile admits
positive fills only. A small debt can round the capped slice to zero in
the source arithmetic, and the native profile rejects that purchase.

Input 0 authenticates the actual state script and amount, including the
internal key, empty Taproot path and current executable leaf. The active
state carries the auction identity, remaining lot, remaining debt, proceeds
already collected, initial bounds, epoch and last accepted event. Its value
is `10,000 + remainingLot * 100`. Its debt accounting preserves
`remainingDebt + collected = initialDebt`.

Kick requires the ward and an actual urn-script collateral input of exactly
`initialLot * 100`. It derives the auction ID from the actual raw setup
outpoint, initial lot and target under a native tag. The index is encoded as
a big-endian integer in this application transcript. A take needs the bidder
signature and an actual bidder-script input of exactly `owe`. Kick and take
require three distinct inputs, including their independent fee input. Redo
and yank need the state and independent fee inputs. Every transition checks
the exact count and amount of the outputs and binds all recipient scripts.

The bidder or ward signs `sig_all_hash` and the explicit action fields under
an action tag. The event authority separately signs `sig_all_hash`, auction
ID, action mode, event clock and normalized curve price under an event tag.
The program checks the signed quote against the actual curve and requires a
nondecreasing event clock. The authority attests the valuation at signing.
The event clock is the bounded source of elapsed time, and the signed
transaction can confirm later. Redo additionally requires the configured ward
and a valid reset event, sets a new epoch, and preserves the rest of the sale.
The source allows a public redo after reset is required. The ward requirement
is the authorization policy of this native profile.

| Linked positive sequence | Exact state value | Actual payout outputs in order |
| --- | ---: | --- |
| Kick 120 units with target 8,301 | 22,000 sats | |
| Buy 30 units at 90 | 19,000 sats | 3,000 to bidder, 2,700 to debt sink |
| Dust-adjusted buy at 80 | 13,300 sats | 5,700 to bidder, 4,601 to debt sink |
| Debt-capped buy at 75 | Terminal | 1,300 to bidder, 1,000 to debt sink, 2,000 to urn, 10,000 carrier |

The dust-adjusted payment of 4,601 buys 57 whole units, while 57 times 80
is 4,560. The capped payment of 1,000 buys 13 units, while 13 times 75 is
975. The vectors reject both smaller payments even with balanced transactions.
Other accepted branches exhaust the lot with residual uncollected debt,
clear exact debt with surplus, restart below cusp or at zero price, purchase
at the reset epoch's price, and yank the remaining collateral to the ward.
Debt clearance returns surplus to the original urn. Lot exhaustion and yank
also end the auction. Every terminal branch returns the separate setup
carrier and consumes the state without a successor.

The fixed configuration uses zero `tip` and `chip`, fixed top and one sale.
The scope covers native collateral and quote accounting. Foreign Vat credit,
Dog accumulators, callback execution, dynamic price feeds and global auction
registry behavior are outside this profile. One aggregate witness carries the
opened state, action and signatures, and native expressions derive the next
state and payment plan from that data.

The synthetic setup, collateral and fee inputs serve as fixture funding
coins. Successors use the raw txids of the actual preceding fixtures. For
accepted spends, the driver checks wire serialization, linked ancestry,
actual C and Haskell primitives and 1,000-sat fee conservation. It compares
the curve at 112 elapsed values and compares fills at 248 bounded inputs.

The frozen 8 GiB diagnostic exited successfully. All 51 full vectors passed
under CMR `ee80b031a3abcd3a5eb56d09e2927661ced579cca00a1ffbb35310b81d30b519`.
That includes 16 accepts and 35 rejects. All 112 curve, 248 fill and 16 linked
wire checks passed. The RTS reported 157.491 seconds elapsed,
1,864,806,944 bytes maximum residency and 4,587 MiB total memory in use.
These are host diagnostic measurements. The log and provenance record bind
the results to the frozen 37-file source closure, primary inputs and binary.
[Vector and RTS log](data/clipper-full51-8g-rts.txt)
[Run provenance](data/clipper-full51-8g-provenance.json)

Build and run the diagnostic from `jet-discovery/` with GHC 9.8.4.

```sh
ghc -O1 -w -threaded -rtsopts -isrc \
  -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery \
  -outputdir /private/tmp/clipper-build tools/ClipperSmoke.hs \
  -o /private/tmp/clipper-smoke
python3 tools/run_clipper_vectors.py
```

The diagnostic driver uses `-O0` for the wide C/Haskell comparisons. The
kernel uses `-O1`. The run records hashes of the compiled source closure,
pinned primary inputs, executable and log.
