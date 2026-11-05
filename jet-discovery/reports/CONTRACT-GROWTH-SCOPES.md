# Contract growth: independence and deployment audit

The first eight of these nineteen application groups are now registered and
passed84/84 current vectors. Six more native implementations typecheck with121
application vectors pending; the DODO private-pool draft also typechecks with31
pending application vectors and26 arithmetic helper passes. The final four
priority application scopes remain gated on complete source math and state
transitions. Helper/parameter variants receive
no extra application count. Exact current source hashes and all retained
attempts are in CONTRACT-GROWTH-VALIDATION.md and its freeze metadata.
Each row describes a complete bounded spend/state predicate to implement, rather
than a new name for an existing kernel. The scopes were compared with every ID in
`reports/data/corpus-metadata.tsv`, the 72-row growth backlog, and the BitcoinGrowth
ownership list supplied by the BIP agent. BitcoinGrowth owns offered HTLC, Ark
refresh, OP_EVICT, numeric DLC, BOLT12, silent payments, BIP322, reserve ownership,
and SPV payment receipt; none is claimed here. LiteratureApps owns its three
crypto-payment wrappers; none is claimed here.

Source coverage: all **30 named primary files across16 repositories** in
`vendor-specs/contract-growth/provenance.json` were retrieved at immutable commits
and inspected for the named functions/state fields below. This is a scoped source
audit, not a whole-repository or complete-protocol audit. Unauthenticated GitHub
API requests first returned HTTP403 rate limits. The GitHub connector resolved
all16 exact branch commits and the complete, untruncated trees needed for path
disambiguation; raw pinned files then downloaded successfully with no remaining
retrieval gaps. An initially guessed Curve filename no longer exists: the actual
sources are `TwocryptoMath.vy` and `Twocrypto.vy`. Rust CLI/generated/test copies
were excluded in favor of the actual on-chain program files. Sources are inert
data, never executed. Per-file source URLs, SHA256, revision and retrieved license
files are retained. A missing license is not treated as a permissive grant.

## Common enforcement model

Every proposed native application must open the current state with `Lib.State`,
consume each logical witness once, enforce the same executable continuation,
conserve actual native satoshis, authenticate every actor, and bind every payout
script/value. Every action of one application is one group, never one count per
branch, user, tree depth, threshold or parameter. Mandatory negative vectors cover
forged old state, altered output, arithmetic boundaries, authorization and replay.

Two-asset protocols require an explicit representation. The proposed deployment
is a serialized covenant ledger of **claims against native BTC collateral**, with
two named claim classes and authenticated user balances/LP or position ownership.
It must implement issuance, transfer, destruction and redemption for those claims
within the same application state machine. They are not independent Bitcoin
assets and are not foreign ERC20/SPL balances. If that complete claim model is not
implemented, pool/order arithmetic receives component credit only and the full
application row remains pending. Shared claim-ledger plumbing is not counted as
another application.

**LMSR backing exception:** the prediction market uses two mutually exclusive
conditional outcome claims. Before resolution, collateral must cover the larger
outcome supply (plus separately owed market fees), rather than their sum. One
source complete-set split deposits one collateral unit and creates one claim for
each outcome; only the winning claim pays. Imposing independent-coupon sum
backing would change the published trade economics. After one authenticated
resolution, collateral covers the remaining winning supply plus fee credits.
All pool and both-owner inventories remain in the committed ledger, with funded
initial subsidy/reserve, exact complete-set mint/merge and signed buy/sell cost
and fee rounding. This exception is one full market family, not extra credit for
claim plumbing, an oracle outcome or a math helper. It does not imply foreign
BN254 collection-ID or global ConditionalTokens storage compatibility.

`nLockTime` is a chosen lower bound, not current chain time. A protocol requiring
an upper deadline cannot be claimed exact using `txLockTime<=deadline`. Auction
phases may instead advance through an explicit auctioneer-signed monotone phase;
interest, OCR and term markets may use a named signed event/height report. Those
are complete **oracle/administrator-authorized native adaptations**, not current
foreign-state equivalence. Exact timestamp equivalence remains gated on an
appropriate trusted current-time/consensus interface.

## Proposed distinct predicates

| Priority / proposed ID | Primary specification and inspected computation | Complete bounded application scope | Independence from current corpus / decisive negatives | Remaining implementation gate |
| --- | --- | --- | --- | --- |
| 1 `app-tokenized-native-vault` | [ERC4626](https://eips.ethereum.org/EIPS/eip-4626): `deposit`, `mint`, `withdraw`, `redeem`, preview rounding | Two-account nontransferable share vault; real BTC deposits/withdrawals, committed account shares/total supply, floor deposit/redeem and ceiling mint/withdraw, authorized share transfer or explicitly nontransferable interface, initial-supply and donation cases | Pool balances are denominated shares with a variable asset/share ratio, unlike a direct payment balance or reserve floor. Reject wrong rounding, dilutive mint, unauthorized burn, fabricated deposit and zero-supply division | Define and test all four actions together; do not count a single conversion formula as the vault |
| 2 `app-asynchronous-vault-claims` | [ERC7540](https://eips.ethereum.org/EIPS/eip-7540): request lifecycle, controller/operator and request IDs | Serialized two-controller vault; funded deposit/redeem request, pending-to-claimable batch fulfillment at one signed rate, partial pull claim, one-use claim accounting and operator changes | Introduces an escrowed request lifecycle absent from synchronous shares and bitmap airdrops. Reject skipped pending/claimable state, double/over claim, wrong controller and unequal rate within one request ID | Include synchronous underlying share logic; rate fulfillment is an explicit vault authority, not proven external yield |
| 3 `app-ascending-auction-escrow` | [Solidity SimpleAuction](https://docs.soliditylang.org/en/latest/solidity-by-example.html#simple-open-auction): `bid`, `withdraw`, `auctionEnd` | Two bidder accounts plus beneficiary; funded strictly increasing bid, authenticated outbid refund credit/withdrawal, monotone close and exact beneficiary payment; remaining loser credit preserved | Stateful highest-bid replacement/refund accounting differs from existing Dutch fixed-price sale. Reject equal/lower bid, unfunded increase, repeated refund and close-state rebid | Native explicit signed close phase; exact foreign wall-clock cutoff is not claimed |
| 4 `app-sealed-bid-auction-escrow` | [Solidity BlindAuction](https://docs.soliditylang.org/en/latest/solidity-by-example.html#blind-auction): commitment, fake/reveal and refund rules | Fixed two bidder commitments/deposits, commit/reveal/closed phases, exact hash(value,fake,secret), bounded once-only reveals, highest valid bid, loser/excess refunds and final beneficiary payment | Secret opening, fake-bid and deposit coverage create a different spend relation from ascending/Dutch auction or HTLC. Reject substituted secret, uncovered bid, duplicate reveal, premature winner and duplicate refund | Same explicit signed phase model; no unauthenticated current-time witness |
| 5 `app-squads-proposal-execution` | [Squads V4](https://github.com/Squads-Protocol/v4): `proposal_create`, `proposal_approve/reject/cancel`, `vault_transaction_execute` | Fixed member set with propose/vote/execute roles; one indexed draft/active/approved/rejected/cancelled/executed proposal, unique voter bitmaps, stale-index check, CSV delay after approval and committed native payout template | The proposal is approved over multiple spends and later executed once; this is not a new k-of-n parameter for current multisig. Reject duplicate vote, wrong role/status, stale proposal, early execute and substituted payout | Include source proposal-state helpers and exact rejection/cancellation thresholds before implementation; BIP340 role-key adaptation is explicit |
| 6 `app-vaa-bridge-replay-payout` | [Wormhole Messages/Bridge](https://github.com/wormhole-foundation/wormhole): `parseVM`, `verifySignatures`, `_completeTransfer` | Fixed guardian set and bounded transfer payload; exact double-Keccak VAA signatures, emitter/chain/guardian-set verification, committed sequence bitmap, recipient/token/amount parsing, collateral debit and one native payout | Current quorum component has no replay ledger, payload-to-payment relation or persistent bridge balance. Reject reused sequence, changed emitter/recipient/amount and duplicate guardian | Define finite accepted sequence range with explicit exhaustion behavior; no source-chain finality beyond guardian attestations; native collateral bridge is not foreign token issuance |
| 7 `app-compressed-asset-transfer` | [Bubblegum V1](https://github.com/metaplex-foundation/mpl-bubblegum): `transfer_v1`, `LeafSchema::to_node` | Bounded authenticated asset tree; full version/ID/owner/delegate/nonce/data/creator leaf encoding, valid old opening, owner or delegate authorization, same metadata/nonce and new owner=delegate, new root in continuation | Existing Keccak path authenticates a leaf but neither validates schema nor transfers ownership. Reject nonowner, changed metadata/nonce, wrong new delegate and forged root | Use a fixed initialized asset ID (do not pretend to derive Solana PDA without implementing it); BIP340 owner-key adaptation must be labelled |
| 8 `app-permit2-bitmap-transfer` | [Permit2 SignatureTransfer/PermitHash](https://github.com/Uniswap/permit2): `_permitTransferFrom`, bitmap positions and `_useUnorderedNonce` | Native reserve with one owner; exact EIP712 witness-transfer authorization, word/bit nonce consumption, amount<=signed maximum, designated spender authorization, committed recipient, partial amount within a finite64-nonce transfer window | Adds an unordered signed-transfer authorization lifecycle absent from ERC2612 component or eligibility airdrop; reject consumed bit, wrong spender/witness, excessive amount and nonce resurrection | Signed deadline has no enforced upper-time expiry; explicit invalidation and owner recovery are unsupported. One initialized reserve lineage, finite64-bit bitmap, opaque fixed native adapter domain; no global Permit2 mapping or exact EIP712Domain interoperability claim. Never infer expiry from low nLockTime |
| 9 `app-conditional-position-partitions` | [ConditionalTokens](https://github.com/gnosis/conditional-tokens-contracts): `reportPayouts`, `splitPosition`, `mergePositions`, `redeemPositions` | One implicit three-outcome condition in an initialized UTXO lineage, six fixed subset-mask balance slots and two owners; disjoint complete/subset partition validation, collateralized creation/burn/transfer, once-only oracle resolution and exact weighted redemption | Existing binary pro-rata collateral payout has no partition/position ledger or split/merge inverse. Reject overlapping/trivial partition, split inflation, merge missing leg, double resolution/redemption | Complete bounded native app29/29PASS. Identity is implicit lineage+mask slot: no implemented question/domain hash, exported position-ID bytes, foreign BN254 collection ID, ERC1155 interface or global registry |
| 10 `app-batch-limit-order-settlement` | [CoW GPv2Settlement](https://github.com/cowprotocol/contracts): `computeTradeExecution`, fill state, limit/fee constraints | Two named collateralized claim classes, two users/orders and one authorized solver; signed order domain, shared clearing prices, side-dependent limit and proportional fee rounding, partial-fill counter/nonces, balance updates and native withdrawal | More than internal transfer: jointly enforces signed limits, common prices and cumulative fills. Reject unfavorable price, overfill, wrong order domain, imbalance and repeated full fill | Full claim ledger and exact supported flags; arbitrary callbacks and a general EVM are excluded, not silently emulated |
| 11 `app-interest-accruing-loan-rollover` | [Compound CToken](https://github.com/compound-finance/compound-protocol/blob/master/contracts/CToken.sol): `accrueInterest`, borrow balance/index, reserve factor | One funded lender/borrower native loan; signed monotone height/rate event, cash+borrows+reserves/index update, debt repayment, lender-share accounting, borrower collateral continuation and eventual liquidation/close | Existing liquidation uses fixed debt; new debt/index/reserve accrual is persistent arithmetic with an authenticated event. Reject replayed height, excess rate, stale index, reserve misrounding and unpaid close | Entire bounded loan lifecycle must fit explicit collateral/debt model; no assertion that a signed height equals current tip |
| 12 `app-ocr-report-state-machine` | [libocr OCR2Aggregator](https://github.com/smartcontractkit/libocr/blob/master/contract2/OCR2Aggregator.sol): `transmit`, `_decodeReport`, config digest and epoch/round | Fixed signer/transmitter config, exact report/context digest and ECDSA signer uniqueness, strictly increasing epoch/round, ordered observations/median rule, persistent accepted answer and payout tied to it | Current median has three independent Schnorr observations and fixed context, with no OCR report transcript/config/replay checks. Reject stale epoch/round, wrong config, duplicate signer and malformed report | Inspect imported OCR signer/config helpers and exact report codec before claiming wire compatibility; latest external oracle freshness still external |
| 13 `app-stableswap-pool-transition` | [Curve3pool](https://github.com/curvefi/curve-contract/blob/master/contracts/pools/3pool/StableSwap3Pool.vy): `get_D`, `get_y`, `exchange`, mint/burn | Three collateralized claim reserves, initialized LP claims; full convergent Newton swap quote with fees/rounding, real claim reserve transition, deposit/withdraw LP issuance/burn and native collateral redemption | Existing kernel computes only invariant D. Reject nonconvergence, optimistic y rounding, reserve underflow, wrong fees, LP inflation and unbacked claims | Claim ledger plus get_y and all bounded pool actions; no count for wrapping get_D in a signature |
| 14 `app-weighted-pool-transition` | [Balancer WeightedMath](https://github.com/balancer/balancer-v2-monorepo/blob/master/pkg/pool-weighted/contracts/WeightedMath.sol): invariant, out-given-in and join/exit, LogExpMath | Two collateralized claim classes with unequal fixed weights, exact fixed-point power/rounding bounds, fees, max-in/out ratios, reserve update and LP join/exit ownership | Unequal weighted exponent is distinct from Uniswap product or Curve Newton. Reject pow-domain breach, downward output error, ratio-cap violation and LP inflation | Port actual log/exp error policy and full claim/LP conservation; simple equal-weight specialization would merge with current constant product |
| 15 `app-cryptoswap-transition` | [Curve TwocryptoMath/Twocrypto](https://github.com/curvefi/twocrypto-ng/tree/main/contracts/main): `newton_D`, `get_y`, `_exchange`, `tweak_price`, wad_exp | Two claim reserves, gamma/A invariant, convergence bounds, fee calculation and authenticated price-scale/profit update, LP conservation and native claim redemption | Distinct from StableSwap via crypto invariant, dynamic fee, price scale and profit guard; reject unconverged math, invalid gamma, forged price scale and profit decrease | Full source time/price EMA dependency must use explicit authenticated events; porting only newton_D is a component |
| 16 `app-proactive-market-maker-private-pool` | [DODO PMMPricing/DODOMath](https://github.com/DODOEX/contractV2/tree/main/contracts/lib), selected DPP trader/storage/vault path: target adjustment, ROne/RAbove/RBelow and quadratic/integral quotes | Two fully BTC-backed claim reserves, owner-signed reference-price/reset/funding/withdraw, fixed k0.1 and zero source fee configuration; both sell directions, exact crossings/caps and direction-specific target storage. Private pool has no synthetic LP issuance; complete coupon issue/transfer/maturity burn remains enforced | Inventory-regime transition and quadratic/integral pricing differ from constant-product/weighted/StableSwap. Reject wrong regime/target, bad quote, unauthorized inventory withdrawal, one-sided close and unbacked claims | NativePmmPool31 application vectors and PMM14 helper vectors pending; DodoMath26 arithmetic vectorsPASS. DVM is not substituted for the full three-regime DPP profile |
| 17 `app-concentrated-pool-swap` | [Uniswap V3 Pool/SwapMath](https://github.com/Uniswap/v3-core): `swap`, tick crossing, fee growth and LP mint/burn | Two claim classes, finite initialized tick map, exact swap steps with crossing/liquidity-net updates, fees, position accounting/collect and collateralized claim outputs | Current TickMath kernel never updates price/liquidity/fees or positions. Reject skipped initialized tick, wrong fee growth, bad price limit and unauthorized position burn | Finite map must cover every initialized tick in its stated domain and reject unsupported traversal; no fabricated unconstrained tick/liquidity witness |
| 18 `app-pendle-term-market-transition` | [Pendle MarketMathCore/LogExpMath](https://github.com/pendle-finance/pendle-core-v2-public): `getMarketPreCompute`, `calcTrade`, `_getLnImpliedRate`, state update | Fully collateralized principal/yield claim ledger with fixed maturity, signed monotone event time/index, exact logit/rate exp/ln trade and fee reserve update, LP actions and maturity redemption | Distinct nonlinear term-rate math absent from funding arithmetic; reject invalid proportion, expired trade phase, incorrect signed index and unbacked principal/yield redemption | Requires complete principal/yield backing and imported PYIndex/fixed-point helpers; a fixed exp/ln output alone is a kernel |
| 19 `app-lmsr-prediction-market` | [Gnosis LMSRMarketMaker](https://github.com/gnosis/conditional-tokens-market-makers/blob/master/contracts/LMSRMarketMaker.sol): `calcNetCost`, offset sum-exp and marginal price | Fixed two-outcome collateralized position ledger, funding parameter, full bounded buy/sell cost using the source192.64 estimation modes, fees and terminal oracle redemption | Conditional tokens split/merge does not price a market; log-sum-exp and offset stability create independent expensive relations. Reject cheapened buy, overpriced sell, wrong offset/rounding and payout without burning positions | Complete imported Fixed192x64Math and position collateral accounting; do not replace published math with floating-point approximations |

The completed first implementation batch comprises the synchronous/asynchronous native
vaults, both explicit-phase auctions, Squads proposal lifecycle, Wormhole replay
payout, compressed-asset ownership transfer, and Permit2 native transfers. These
have direct serialized-state deployments without pretending that two independent
Bitcoin assets already exist. The remaining eleven require deeper arithmetic or
full collateralized-claim machinery; the six compact native drafts and DPP draft
are still uncredited pending full vectors. All nineteen require real
positive and negative vectors, CMR invariance, witness dataflow review and a fresh
measurement before inclusion in any achieved-count or recommendation table.
