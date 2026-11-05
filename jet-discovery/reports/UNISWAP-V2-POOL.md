# Native Uniswap V2 pool with protocol fee minting

`app-uniswap-v2-fee-on-pool` passed all **32 actual native vectors** under one
canonical CMR, `e591f9a828913283aa8d6eba7a6e829e2e9ac59e868716c855a1c3416b8e1db7`.
It is one complete bounded application with two funded native coupon classes,
two ordinary owners, and a fixed fee recipient and fee setter. Its source is
[UniswapV2Pair.sol at 6a9e7c9](https://github.com/Uniswap/v2-core/blob/6a9e7c97860676e0992f22a49665760444c1cdf5/contracts/UniswapV2Pair.sol)
and the matching [Math.sol](../vendor-specs/uniswap-v2/Math.sol).
The source/license and exact hashes are retained as inert data in the
[contract source packet](../vendor-specs/contract-extras/provenance.json) and
[math dependency manifest](../vendor-specs/uniswap-v2/manifest.json). No
external code is executed.

| Transition | Source arithmetic | Native enforcement |
| --- | --- | --- |
| Fund and redeem | Native asset setup, separate from foreign ERC20 issuance | Actual input 1 funds the exact deposit and fee. A withdrawal burns that owner's coupons and pays the exact script and amount. A and B have distinct fixed lower maturities. |
| Initial join | Mint `floor(sqrt(a*b)) - 1000` to the provider and lock exactly 1,000 LP units | Both owner balances decrease by the contributed amount; reserves, outstanding shares and locked LP are committed. |
| Later join | Mint the smaller floor of `amount * adjustedSupply / reserve` | Unequal deposits are allowed; both actual reserves grow while only the floor share count is credited. |
| Swap | Require `(1000 * x - 3 * input) * (1000 * y) >= 1000000 * oldA * oldB`, with the sides reversed for B → A | Debits/credits and both reserve changes are enforced; the chosen output must be positive and below its reserve. Swaps do not update `kLast`. |
| Protocol fee | If enabled and `rootK > rootKLast > 0`, mint `floor(supply * (rootK-rootKLast) / (5*rootK+rootKLast))` to the fixed fee account before join/exit arithmetic | Root values are computed on chain by a 22-step restoring integer square root, with no witness root hint. A fee toggle alone preserves `kLast`; the next off-mode mint/burn resets it. |
| Exit | Burn existing owned LP and return both `floor(burn * reserve / adjustedSupply)` amounts | LP and owner coupons update atomically; the fee recipient may burn its previously minted LP. Locked LP cannot be spent. |

Each coupon class has at most `2^22 - 1` outstanding units, so even the
largest fee-adjusted K products fit 64 bits. Products, quotient divisors,
additions and subtractions are checked. A single aggregate witness opens the
old state and the proposed next state exactly once. The program requires
current input 0, exact current script and value, exactly two inputs, signed
owner or fee-setter authorization on the actual transaction, and a successor
that commits every changed and unchanged field under the same executable leaf.
Both coupon classes' liabilities, including pool reserves, are BTC-backed.
The 1,000 sat carrier is separate from both classes and is preserved.

The 16 positive and 16 negative vectors cover both swap directions, first and
unbalanced joins, actual fee dilution, partial and full-owner exit, fee-LP
exit, fee toggle/reset, actual coupon withdrawal, rounding at the swap limit,
unauthorized fee change, underfunding, incorrect state, and a re-signed diverted
payout. The positive chain derives its state outpoints from actual previous
transaction wire. The square-root probe independently compares 34 native
boundary inputs against an Integer binary-search reference and rejects the
exclusive range boundary. The arithmetic and fee tests are not extra groups.

The [native log](data/uniswap-v2-full32-16g.txt) and
[run record](data/uniswap-v2-full32-16g.json) show actual exit 0, 132.650 seconds
elapsed and 2,492,007,480 bytes maximum live residency at `-N1 -A16m -M16G`.
All 32 vectors used the canonical prepared path. Recompile
`tools/UniswapV2PoolProbe.hs` with the local package database as described in
[CRYPTO-FAMILIES.md](CRYPTO-FAMILIES.md). Shared cost/mining is still pending.

This is one initialized native pool. It has no arbitrary foreign assets,
flash callback, LP token transfer, reconfiguration of the fee recipient,
foreign token behavior, cumulative timestamp price oracle, skim or sync.
Funding the initial carrier and authorization of the external funding/fee
input remain ordinary transaction responsibilities.
