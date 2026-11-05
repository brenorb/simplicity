# Native claim representation for the remaining contract scopes

This model now supports **one qualified complete native conditional-position
application with29/29 actual guarded vectorsPASS**, registered as
`app-conditional-position-partitions`. The shared representation/plumbing has
**zero separate application credit**. All other unvalidated drafts remain gated.
Exact evidence and source hashes are in `NATIVE-PROTOCOLS-VALIDATION.md` and
`data/claim-full29-freeze.json`. Source formulas and native asset representation must be reported
separately; implementing a native representation does not establish ERC20/SPL
wire compatibility or a foreign protocol's global state.

The base representation has two independently BTC-backed receipt classes, A and
B, with different fixed lower redemption heights. One state UTXO commits every
supported account balance, pool reserve, fee holding, class supply, LP ownership
and nonce. The bounded deployment has exactly two user accounts. No externally
circulating token UTXO or uncommitted account database is assumed.

The native collateral and class invariants, checked on each applicable old and
new state, are:

* Native value excludes the explicitly reserved state carrier and must be at
  least `totalA + totalB`. Checked addition rejects wraparound.
* Each class supply equals its two user balances plus pool reserves, fee
  holdings and any explicitly named escrow. A balance cannot be simultaneously
  counted as user-owned, held by a pool, and escrowed.
* Issuing a receipt increases its supply and the actor's balance only when an
  actual additional transaction input funds the native collateral increase.
* Transfers require the debited account's transaction signature and preserve
  class supply, native collateral and every uninvolved balance.
* Redeeming a receipt burns the actor's owned balance and class supply, checks
  the class's lower-height lock, decreases native collateral by the same amount,
  and binds the actual recipient script/value.
* Pool swaps move claims between authenticated user balances and reserves;
  protocol-specific fees are accounted for explicitly. They create no native
  collateral or receipt supply.
* LP tokens are ownership records over those same pool reserves. Minting/burning
  LP ownership follows the published pool formula and debits/credits the actual
  claim reserves. LP supply equals committed LP account balances. LP balances
  are not counted as an additional independent native collateral liability.
* Every action requires the actual current input0, increments a checked state nonce, authenticates old state, and
  commits the complete successor under the same executable leaf. Spending the
  one current state UTXO serializes actions and prevents replay of a consumed
  reserve/claim state.

Conditional positions and market-maker outcome inventory require an additional
layer. Underlying A held by a condition is an explicit A escrow; splitting it
does not create more native A supply. Outcome positions are claims on that
escrow with oracle-dependent payouts, rather than independently BTC-redeemable
A/B receipts. For the completed bounded condition, outstanding position quantities
covering each possible outcome remain bounded by the escrow before resolution.
After resolution, exact weighted numerator liability is bounded by escrow times
the payout denominator. Split,
merge, transfer and redemption must update all position ownership and burn
redeemed positions. The native backing invariant is checked against the existing
A/B supply; the same underlying escrow is never minted a second time. This
layer is enforced by the29-vector conditional-position application. Condition
identity is implicit in the initialized UTXO lineage and six subset-mask balance
slots, with a fixed oracle signing the actual transaction/state. No explicit
question/domain hash, exported position-ID bytes, foreign BN254 collection ID,
ERC1155 interface or global registry is implemented by that application.

The proposed LMSR application uses two mutually exclusive conditional outcomes,
rather than independently redeemable A/B receipts. A source complete-set split
deposits one collateral unit and creates one claim for each outcome, of which
only the winner pays. Consequently its collateral must cover the larger total
outcome supply plus separately owed fee credits before resolution; after one
authenticated resolution, it covers winning claims plus fees. Requiring their
sum would change the published LMSR trade/complete-set economics. All pool and
both-owner inventories, funded initial subsidy, exact signed cost/fee rounding,
committed condition/oracle identity, actual payments and burn-before-redemption
remain required. This distinct complete market is still gated on full native
application vectors; its cost/exp/log helpers receive no application credit.

All arithmetic-heavy scopes must execute their actual published bounded math:
Curve `get_y` and convergence/rounding, Balancer weighted power/error bounds,
DODO's three inventory regimes and crossing logic, concentrated liquidity tick
and fee transitions, Pendle rate logit/exp/ln, and LMSR offset/estimation modes.
Reusing the receipt plumbing does not make these applications interchangeable,
and the plumbing itself receives no program count. A formula-only path retains
component status until the complete applicable accounting transition is enforced.

Fixed maturity lower bounds are enforceable through CLTV. An upper-time trading
deadline, latest oracle event or current foreign lending index needs a separate
authenticated model; chosen `nLockTime` cannot supply that fact. A signed phase,
rate/index or configuration event must name its issuer and replay scope. Sources
and imported helpers must be pinned and inspected before their compatibility
claims are made. An unresolved asset or mathematical gate stays explicit rather
than being replaced with a witness-provided quote or unchecked new reserve.

The native StableSwap deployment extends this exact accounting to three coupon
classes A/B/C, with redemption lower heights800000/900000/1000000. All six user
balances, three reserves, three admin fee holdings and three supplies are in the
committed state. Its physical collateral must cover `totalA+totalB+totalC` with
checked additions. LP ownership covers those reserves and is not a fourth native
liability. Equal native normalization replaces the foreign coins' decimal rates.
