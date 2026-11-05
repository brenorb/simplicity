# Funded native quadratic matching round

`app-budgeted-quadratic-funding` passes all **42 native vectors** and implements one bounded Bitcoin round with three fixed donor keys, two project recipients, and one sponsor. The current state is funded with BTC, contribution amounts are calculated on chain, and each nonzero project or sponsor payout can be withdrawn once. The allocation helper adds no separate corpus group. Fresh shared cost and mining remain pending.

## Source relation and native policy

[Buterin, Hitzig and Weyl, *A Flexible Design for Funding Public Goods*, arXiv:1809.06421v2](https://arxiv.org/html/1809.06421v2#S5.SS1) §5.1, Definition 5.1, blends squared sums of contribution square roots with direct contributions using one coefficient α. For project p, write its direct sum as Cₚ and its unconstrained matching deficit as Dₚ. The paper's formula is Cₚ + αDₚ. The same section discusses choosing α to satisfy the sponsor budget. The reviewed paper is linked, not redistributed or executed. [Gitcoin MatchPayouts](https://github.com/gitcoinco/matching_contracts/blob/ae4e44e912531669a8115386ffd97af2f47f9fd1/contracts/MatchPayouts.sol) is an approved-payout contract, not the source of the matching formula. Its scope and license gap are recorded in [the earlier feasibility audit](CONTRACT-EXTRA-SCOPE-AUDIT.md).

The native profile stores six integer voice counts v ∈ [0,63]. Each fixed donor's cumulative contribution to each project is exactly v² sat, so its nonnegative square root is v. Increasing the count costs v_new² − v_old². Splitting a contribution into consecutive updates therefore costs the same as contributing the final square directly. Project matching is computed from three donor histories, not from a list of individual payments.

Let B ∈ [1,65535] be the sponsor's already funded satoshi budget. For each project:

```text
Cₚ = sum(vᵢ²)
Dₚ = sum(vᵢ)² − Cₚ
D  = D₀ + D₁
Mₚ = 0                                  if D = 0
Mₚ = floor(min(B,D) × Dₚ / D)             otherwise
project payouts = C₀ + M₀, C₁ + M₁
sponsor payout  = B − M₀ − M₁
```

Choosing α = min(1,B/D) at close and rounding each project match down to satoshis is an explicit native policy. When D ≤ B the matching deficits are paid exactly; when D > B, any aggregate floor remainder (at most one sat for two projects) belongs to the sponsor. When D = 0 there is no match and the sponsor recovers all B. No actor can redirect the remainder or overwrite the computed allocation. The independent Integer model derives Dₚ from twice the sum of cross products, an algebraically equivalent expression.

The largest direct sum for one project is 11,907 sat, the largest Dₚ is 23,814, and D ≤ 47,628. Thus `min(B,D) × Dₚ ≤ 1,134,213,192` and fits Word32, as do all intermediate additions and subtractions of funded amounts. A project receives at most 35,721 sat; the two project amounts and the sponsor remainder fit the three Word16 claim slots. The whole open or closed ledger holds at most 89,349 sat. Positive division is a full quotient/remainder relation; D = 0 bypasses it.

## Bitcoin state transitions

| Current state | Action and authority | Exact continuation or payout |
| --- | --- | --- |
| Funded open | A chosen donor signs the actual `sig_all_hash`. Input 1 uses the fixed script for that donor and supplies the square difference plus the fixed 1,000-sat fee. The selected voice slot must increase within bounds. | Output 0 is the same leaf and new committed voice ledger, with old value plus the exact square difference. No second output. |
| Funded open | Sponsor signs the actual `sig_all_hash` to close. Input 1 supplies the fee only. | Output 0 preserves every funded satoshi and commits the three computed remaining claims. The voice ledger cannot be reopened. |
| Closed | Anyone may request one positive claim, with a fee input. | Exact fixed recipient and amount. The selected slot becomes zero. Output 0 continues the ledger and output 1 pays the claim while any balance remains; the terminal claim pays at output 0 with no continuation. |

Every branch requires **CurrentIndex 0**, exactly two inputs, an actual current input script matching the state leaf, and current value equal to the committed ledger balance. The initial sponsor deposit establishes a particular round lineage with zero votes. Two independent funding transactions can initialize distinct lineages; the program does not impose a global registry. The NUMS-derived Taproot internal key binds the 32-byte tagged state, and the program requires the expected single leaf without a Taproot path. Each subsequent output retains that leaf. The aggregate witness enters once. Signatures, matching amounts, claims, and output scripts use projections of that same state and action, with no repeated witness hint.

The current-input predicate does not authorize input 1 on its own: consensus must verify that input separately. It prevents extracting fees or donations from the protected balance. One fixture constructs two identical funded inputs competing for the same payout; input 0 can satisfy its own predicate while input 1 cannot. The three fixed keys identify the roster but cannot establish human identity, prevent collusion, or prove Sybil resistance; those limitations are discussed in the paper's §5.2. Closure is an explicit sponsor action without a deadline. Small exact payout fixtures, including the one-sat remainder, measure consensus relations and may fall below relay dust policy.

## Validation

The standalone driver is `tools/QuadraticFundingProbe.hs`; the independent model is `src/JetDiscovery/Ref/QuadraticFunding.hs`. The reference checks capped, uncapped, no-match, and maximum cases; split costs; and all six claim orders. The arithmetic driver compares 24 complete allocations to that model. The full native driver uses genuine continuation scripts, independent transaction fixtures and actual BIP340 signatures. It checks the bound program against canonical composition and requires prepared-path observability on all vectors.

The full suite has 18 accepting and 24 rejection fixtures. It exercises all six donor/project slots. The negatives cover underpaid split contributions, wrong donor/funding script, signature replay and cross-project reuse, cap and strict-increase checks, invalid slot, unauthorized or incorrect closure, zero-match misallocation, wrong phase, wrong payout or continuation, overfunded current state, wrong actual input script, stale witness, repeat claim, and index-1 payout reuse. All native vectors ran through the prepared bound program and kept the same CMR.

The first 4 GiB build passed the reference and all 24 allocation comparisons, but rejected the first expected native positive (actual exit 1). The fixture used the baseline helper that adds the CheckSig domain wrapper, while the QF term checks raw `sig_all_hash`. Only the signature fixture and donor-slot test coverage changed in the retry. The failed first source and log are retained under `reports/data/quadratic-funding-4g-*`.

| Current run, 4 GiB cap | Actual outcome | Wall seconds | Maximum live bytes |
| --- | --- | ---: | ---: |
| Independent Integer model | PASS, exit 0 | 0.40386 | 55,872 |
| Complete allocation arrow comparisons | 24/24 PASS, exit 0 | 3.66269 | 55,143,712 |
| Full native round | **42/42 PASS, exit 0** | **149.95181** | **2,379,113,120** |

The canonical commitment remained
`44d34b304a15c47df051f63d67a7082ab0307acb488d95de8194d9f03abb4f05`
across the fixture correction. The successful native run held 4,160 MiB of RTS
memory, including allocation overhead. The [native log](data/quadratic-funding-current4-native-verification.txt),
[actual statuses](data/quadratic-funding-current4-full-status.json), and
[provenance](data/quadratic-funding-current4-full-provenance.json) record the
binary SHA-256 `516fc30f03afe598b74e3a55a870beb97592c778037a09304c7a24d2b94eaecf`,
compiler settings, and all 35 frozen source files. No frozen source changed
during the successful execution. These are validation resource measurements,
not Simplicity costs.

To reproduce, build the driver with the direct GHC/package flags in [CRYPTO-FAMILIES.md](CRYPTO-FAMILIES.md), then run:

```sh
python3 tools/run_crypto_validation.py --label FRESH-LABEL --binary BINARY \
  --build-dir BUILD-DIR --driver tools/QuadraticFundingProbe.hs --heap 4 \
  --group reference --group allocation --group native \
  --compiler-flags '-O1 -threaded -rtsopts -isrc'
```
