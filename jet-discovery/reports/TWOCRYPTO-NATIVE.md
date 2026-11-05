# Fixed-scale native TwoCrypto pool

The corpus entry app-cryptoswap-transition passes all **56 native vectors**. It carries two independently funded Bitcoin coupon reserves, two registered owners, native LP balances, and a fixed administrator. It supports funded issuance, coupon and LP transfers, initial and fee-bearing joins, both swap directions, proportional LP burns, admin fee settlement, and actual Bitcoin redemption. This is one bounded native state machine.

## Source and arithmetic profile

The pool and math are pinned at Curve TwoCrypto NG revision 5cbe558902402e8fcb331463089db65fc56c11f9. The existing vendor packet records exact source hashes and retains the upstream license. The Vyper is inert reference material. The Integer and Simplicity implementations were written against the source relations. [Pool source](../vendor-specs/contract-growth/curvefi_twocrypto-ng_contracts_main_Twocrypto.vy), [math source](../vendor-specs/contract-growth/curvefi_twocrypto-ng_contracts_main_TwocryptoMath.vy), [vendor provenance](../vendor-specs/contract-growth/provenance.json).

| Parameter | Fixed value or bound |
| --- | --- |
| Amplification and gamma | ANN = 4,000,000 including the source amplification multiplier, gamma = 199 × 10^15 |
| Coupon precision and price scale | Each coupon is one satoshi of backing. Each source balance is normalized by 10^12. WAD and price scale are 10^18. |
| Active reserve and D range | Each reserve is 100,000–4,000,000 sats, D is 10^17–8 × WAD. Empty pools have zero reserves, D and LP supply. |
| Convergence and representation | First source convergence in at most 12 updates, with checked 64-bit and 128-bit intermediates. Values exceeding the checked projection or iteration cap reject. |
| Swap fees | Mid fee 30,000,000, out fee 50,000,000, fee gamma 10^16, fee denominator 10^10. |
| LP accounting | LP supply at most 8 × WAD, virtual price between WAD and 2 × WAD, profit between WAD and 4 × WAD. Profit anchor is between WAD and current profit. |
| Rebalancing | Allowed extra profit = WAD. No A/gamma ramp or parameter updates. |

The source legal ranges and default integer scaling are checked against the same-revision constants and parameter definitions. [Pinned constants](https://raw.githubusercontent.com/curvefi/twocrypto-ng/5cbe558902402e8fcb331463089db65fc56c11f9/contracts/main/constants.vy), [pinned parameter module](https://raw.githubusercontent.com/curvefi/twocrypto-ng/5cbe558902402e8fcb331463089db65fc56c11f9/contracts/main/params.vy).

### Source branch selection

The swap gate requires 45 × D ≤ 100 × x_j ≤ 55 × D, where x_j is the normalized input-side reserve after adding the trade. The proof tool covers this closed interval with 1,000 rational cells. It preserves the source’s signed divisions, including truncation toward zero. It checks the selected coefficient divider is exactly 10^12, the source K0_i guard follows from the interval, and the scaled discriminant is at most −847034541389245239203074749027439079576577. Therefore source get_y takes its _newton_y branch and returns a zero K0_prev throughout the supported interval. The Simplicity term runs that checked Newton recurrence with the original early-exit rules. The invariant D uses the zero-seed path of source newton_D with its integer square-root start and first-convergence comparison. The analytic cube-root path and nonzero K0_prev path are excluded. [Executable interval proof](../tools/check_twocrypto_profile.py), [proof output](data/twocrypto-profile-proof.json).

The checked spot gate uses the original nested rounding for K0 and requires floor(K0/WAD) in [0.95, 1.02) × WAD. The proof covers this range with 700 rational cells. Source GK0 stays at least 24113621198000000000000000000000000, and the checked source spot arithmetic fits the original word width. With WAD ≤ virtual price ≤ 2 × WAD and profit ≥ WAD, the source condition (virtual price − WAD)^2 > profit × WAD is false. The moving-average oracle and spot price are unobserved in this projection, and the source price scale stays fixed. The program persists the exact virtual-price, profit and admin balance values that remain relevant to the supported transitions. It exposes no oracle read API or moving-scale behavior.

### Pool transitions

| Transition | Preserved source behavior and native application |
| --- | --- |
| Initial join | Derive D from both normalized reserves. Mint floor(D/2) at the fixed scale. Initialize virtual price, profit and profit anchor to WAD. Only the authorizing owner receives the LP units. |
| Later join | Compute the raw LP change from Dnew/Dold. Apply the source liquidity-imbalance fee with the exact fee divider, noise fee and final one-unit charge. The fee is deducted from the owner's mint and half is accrued as virtual admin LP. |
| Swap X → Y or Y → X | Solve the other reserve at stored D with the proven get_y branch. Preserve the source one-unit output subtraction, integer normalization, ordered dynamic fee, and minimum-output check. Recompute D with K0_prev = 0. Recalculate virtual price and profit and enforce strict virtual-price improvement. |
| Proportional exit | Burn the owner's exact LP request. A partial burn computes coupon payments and the D decrement with burn−1. A full burn releases both reserves and zeros D. The native minimums apply to either branch. |
| Admin settlement | Calculate the source positive fee share from current versus last-claimed profit and accrued virtual admin LP. Apply source proportional coupon removal, D and price adjustment, profit accounting, anchor update and virtual LP reset. The fixed admin signs a standalone transition. |
| Coupon actions | Exact Bitcoin deposits issue one coupon per satoshi. Coupon transfers and LP transfers stay fully backed. Mature customer and admin coupon redemptions pay the corresponding owner's fixed Bitcoin script and debit the same amount from collateral. |

The positive source admin claim requires at least one whole LP unit and sufficient profit. Native settlement also requires a nonzero calculated fee, share and combined output, and a time-type BIP68 sequence of at least 169 units on the actual state input. That is 86,528 median-time-past seconds from the current state coin. This is a fixed native eligibility rule whose relative age restarts at each continuation. The source uses time since its last admin claim and invokes the calculation from fixed-output or one-coin exits. The native adapter implements the positive settlement arithmetic as its own action and excludes both of those withdrawal modes. Source no-op claims reject in the standalone action. [Pinned pool functions](../vendor-specs/contract-growth/curvefi_twocrypto-ng_contracts_main_Twocrypto.vy), [BIP68](https://github.com/bitcoin/bips/blob/master/bip-0068.mediawiki).

The branch, iteration, range and width checks narrow the application deliberately. Other parameterizations, price ramps, independent external oracle attestations, moving-scale/EMA state, ERC-20 allowance and transfer behavior, callback paths, foreign liquidity, one-coin and fixed-output exits, and factory governance are outside the native profile. The two coupon classes encode fully funded local BTC claims with independent maturity and ownership.

## Bitcoin ownership and state

The initialized pool has a 10,000-sat carrier. Every continuation carries exactly that anchor plus total coupon collateral. The old and next 32-word ledgers each commit both supplies, each owner's two coupon balances, both reserves, the admin's coupon balances, LP supply and ownership, the pool's invariant and fee accounting, and a checked nonce. Both coupon supplies equal the sum of the matching owner, reserve and admin balances. Total collateral equals the sum of both supplies and is capped at 20,000,000 sats. LP supply equals the two owners' LP balances. The reserved words are zero.

One typed witness enters the pure kernel. The old opening must match the Taproot commitment and the actual state input script. The program requires actual input index 0, exactly two distinct prevouts, and the exact input amounts. Input 1 supplies a fixed 1,000-sat fee and any coupon issuance funding. Consensus validates input 1's own authorization. Output 0 must be the exact same-leaf successor script and backing. A redemption adds exactly one payout output, whose value and fixed spendable P2TR script are checked. Owner or admin BIP340 authorization binds the actual transaction through raw sig_all_hash. Coupon classes use nLockTime heights 800,000 and 900,000 as lower bounds. The initialized outpoint defines one pool lineage. The carrier persists after full LP exit or coupon redemption and can anchor another join.

In the main fixture the owners fund 11,000,000 sats of coupons. Alice joins with 3,500,000 sats of each coupon. Bob joins with 300,000 sats of X, then Alice swaps 200,000 X and Bob swaps 330,000 Y. Alice transfers LP ownership and burns part of her remaining LP. The subsequent admin settlement removes 411 X and 406 Y coupons from the pool reserves, and both mature balances redeem to the exact administrator script. The same history exercises a customer transfer and 7,000-sat and 5,000-sat owner payouts. A branch from the same funded origin checks a balanced full exit and the 99,999-sat proportional rounding result.

## Verification

The independent Integer source model is in [Ref.TwoCrypto](../src/JetDiscovery/Ref/TwoCrypto.hs) and the independent cash/ownership model is in [Ref.TwoCryptoLedger](../src/JetDiscovery/Ref/TwoCryptoLedger.hs). The source arithmetic groups passed 36 comparisons for division, invariant, fallback and fee calculation plus the independent source audit. The pool arithmetic groups passed 19 comparisons for joins, both swap directions, exits and admin settlements. Those groups include zero divisors, maximum wide division, both fallback interval edges, one-unit outside failures, positive and invalid initial joins, fee rounding, full and partial burns, and a positive source settlement. [Math results](data/twocrypto-math-8g-full-status.json), [math provenance](data/twocrypto-math-8g-full-provenance.json), [pool results](data/twocrypto-pool-8g-full-status.json), [pool provenance](data/twocrypto-pool-8g-full-provenance.json).

The first 16 GiB native diagnostic verified the same ordinary and prepared-front commitment root and confirmed that the kernel contains no internal witness or delegation. Its fixture was superseded after the independent ledger preflight found that a partial LP burn left insufficient supply for source admin settlement. The process was interrupted before any vector completed. The corrected fixture keeps the same program relation and root. The frozen Haskell source diff starts after the program and entry definitions, in fixture data. [Superseded diagnostic](data/twocrypto-native-16g-native-verification.txt), [actual status](data/twocrypto-native-16g-full-status.json).

The corrected native process passed all 20 acceptances and all 36 rejections. Every case used the prepared kernel under canonical CMR fbcdcf5cd9b0d3a6b7dea641b85de4c02eafa5ce9e7c7d3879071a00a8602a31. The 43 frozen source files and seven recorded runtime data files all matched current bytes. The binary and log hashes also matched the manifest. The actual native child exited 0 after 325.002 seconds. It used 19,314 MiB of RTS memory, with 7,549,024,176 maximum live bytes under the 32 GiB cap. [Native log](data/twocrypto-native-current-32g-native-verification.txt), [actual status](data/twocrypto-native-current-32g-full-status.json), [frozen provenance](data/twocrypto-native-current-32g-full-provenance.json).

The rejections include underfunding, forged reserve, profit and LP balances, wrong ownership and output scripts, early redemption or fee settlement, and repeated admin settlement. The paired current-index control opens two actual inputs with the same state script and value and signs for each input's actual environment. The transaction accepts at index 0 and rejects at index 1. This packet records vector and source proof evidence. Fresh shared cost analysis follows registry integration.

The three drivers are TwoCryptoMathProbe, TwoCryptoPoolProbe and TwoCryptoNativeProbe. Build them with the direct GHC and package flags in [CRYPTO-FAMILIES.md](CRYPTO-FAMILIES.md). Each driver supports only the named groups shown below. Use a fresh label for each replay. The wrapper records the actual child exit status and preserves a frozen source and binary manifest for that invocation.

```sh
python3 tools/check_twocrypto_profile.py
python3 tools/run_crypto_validation.py --label FRESH-MATH --binary MATH-BINARY \
  --build-dir MATH-BUILD --driver tools/TwoCryptoMathProbe.hs --heap 8 \
  --group reference --group division --group invariant --group fallback --group fee
python3 tools/run_crypto_validation.py --label FRESH-POOL --binary POOL-BINARY \
  --build-dir POOL-BUILD --driver tools/TwoCryptoPoolProbe.hs --heap 8 \
  --group joins --group swaps --group exits --group sweeps
python3 tools/run_crypto_validation.py --label FRESH-NATIVE --binary NATIVE-BINARY \
  --build-dir NATIVE-BUILD --driver tools/TwoCryptoNativeProbe.hs --heap 32 --group native
```
