# Native funded mutual cover

`app-native-mutual-insurance` passes all **63 native vectors**. It models two cover policies against a shared Bitcoin capital pool. Each policy can change owner and make successive claims against its remaining coverage. The pool collects premiums, reserves claim deposits, and releases capital only after accounting for both policies. A fixed assessor signs the outcome of each pending claim.

## Pinned source behavior

The source revision is Nexus Mutual `9e885628e9049025bd625cc4cf02d7a981d5c338`. The original packet retains `Cover.sol`, `Claims.sol`, `Assessments.sol`, `IClaims.sol` and the GPL-3.0-only license. The supplemental packet retains exact Git blobs for `CoverNFT.sol`, `AssessmentLib.sol`, `IAssessments.sol`, and `Pool.sol` at that same revision. Source files are inert data. [Original provenance](../vendor-specs/contract-extras/provenance.json), [supplemental provenance](../vendor-specs/nexus-mutual-native/manifest.json).

| Source relation | Pinned evidence |
| --- | --- |
| Purchase assigns a cover NFT owner and collects a premium. The ETH payment branch credits the pool and accounts for commission and remainder separately. | [Cover.sol purchase and payment](../vendor-specs/contract-extras/NexusMutual_smart-contracts_9e885628_contracts_modules_cover_Cover.sol) |
| Cover transfer updates the owner and clears individual approval. The claim payout and deposit retrieval look up the current NFT owner. | [CoverNFT.sol](../vendor-specs/nexus-mutual-native/CoverNFT.sol), [Claims.sol, lines 205–251](../vendor-specs/contract-extras/NexusMutual_smart-contracts_9e885628_contracts_modules_assessment_Claims.sol) |
| Submission checks cover ownership, remaining amount, prior claim eligibility, and the time window. It transfers an exact 0.05 ETH deposit to the pool and starts assessment. | [Claims.sol, lines 127–196](../vendor-specs/contract-extras/NexusMutual_smart-contracts_9e885628_contracts_modules_assessment_Claims.sol) |
| The assigned group votes once per assessor. After the cooldown, more accept votes yield acceptance, more deny votes yield denial, and equal votes yield a draw. | [Assessments.sol](../vendor-specs/contract-extras/NexusMutual_smart-contracts_9e885628_contracts_modules_assessment_Assessments.sol), [AssessmentLib.sol](../vendor-specs/nexus-mutual-native/AssessmentLib.sol) |
| An accepted claim is redeemed once by its current owner. Redemption marks both payout and deposit retrieval, reduces cover by the payout, and returns the deposit with the payout. A draw lets anyone trigger the once-only deposit refund to the current owner. A denied claim forfeits its deposit to the pool. | [Claims.sol, lines 200–251](../vendor-specs/contract-extras/NexusMutual_smart-contracts_9e885628_contracts_modules_assessment_Claims.sol), [Cover.sol, lines 613–652](../vendor-specs/contract-extras/NexusMutual_smart-contracts_9e885628_contracts_modules_cover_Cover.sol), [Pool.sol, lines 255–279](../vendor-specs/nexus-mutual-native/Pool.sol), [Nexus Claims documentation](https://docs.nexusmutual.io/developers/contracts/Claims/) |

## Native policy and exact backing

The initial state is one funded 1,000-sat carrier with two unused policy slots. The provider funds additional underwriting capital from its fixed Bitcoin output script. Each policy slot can be purchased once by one of two registered owners. The owner pays a premium of `ceil(cover / 10)` sats into capital. Each cover can reserve up to 4,000,000 sats. Each claim submission adds a 1,000-sat deposit from the current owner's fixed script.

The ledger reserves deposits separately from underwriting capital. Pending, accepted-unredeemed, and drawn-unrefunded claims each reserve one deposit. The sum of outstanding cover must be at most underwriting capital. The sum of capital and refundable deposits may reach 10,000,000 sats. That combined cap always leaves room to convert an existing deposit to capital on denial. The actual pool input and continuing output each hold exactly the carrier plus the committed capital and the applicable refundable deposits. Funding input 1 supplies the exact required credit plus a fixed 3,000-sat fee. Fee-only transitions require exactly that fee. Consensus validates input 1's own authorization separately.

| Transition | Authorization | Exact BTC and state effects |
| --- | --- | --- |
| Fund | Capital provider | Credit positive actual funding to underwriting capital. |
| Withdraw | Capital provider | Pay a positive amount to its fixed script. Remaining underwriting capital must still cover both policies. Refundable deposits remain reserved. |
| Buy cover | Selected registered owner | Credit the exact premium and set remaining coverage on an unused slot. Validate combined exposure after the purchase. |
| Transfer | Current owner | Move the positive remaining cover, claim ID, claim amount and phase to the other registered owner. BTC backing stays constant. |
| Submit | Current owner | Increment the policy's 16-bit claim ID with no wrap. Set a positive request within remaining cover and reserve the exact deposit. |
| Accept | Assessor | Mark the pending claim redeemable. Retain both the requested amount and deposit reservation. |
| Deny | Assessor | Clear the request, mark denial and convert the deposit to underwriting capital. Coverage stays constant. |
| Draw | Assessor | Mark the pending claim eligible for deposit retrieval. Retain the amount, coverage and deposit reservation. |
| Redeem | Current owner | Pay the exact claim and deposit to that owner's fixed script. Reduce capital and coverage by the claim amount. Clear the request and mark the payout consumed. |
| Retrieve drawn deposit | Permissionless | Pay the deposit only to the current owner's fixed script. Preserve coverage and capital. Clear the request and mark the refund consumed. |
| Surrender | Current owner | Release remaining cover with no refund after all claims in the slot have settled, or before a claim starts. |
| Close pool | Capital provider | With both cover amounts and all deposit reserves zero, pay the carrier and remaining capital to the provider as the only output. |

A 32-byte opening commits the pool's capital and both policies. The tagged layout is `NMX1 || capital_be32 || policy_0 || policy_1`. Each policy is `phase_u8 || owner_u8 || claim_id_be16 || remaining_cover_be32 || request_be32`. The NUMS-derived Taproot internal key binds these bytes. Every transition checks the actual current script, requires input index 0 and exactly two distinct prevouts, and binds the actual continuing and payment scripts and amounts. Signed actions use the actual raw `sig_all_hash`, which binds the old outpoint and the successor's exact script. An assessed verdict therefore binds the claim and outcome through that transaction.

The two policy slots and the two owners are fixed. A slot can hold at most one unsettled claim and accepts a new submission after denial, payout, or deposit retrieval if cover remains. Claim IDs are per-slot, with a maximum of 65,535. Transfers can occur while assessment, payout, or deposit retrieval is pending. The exact current owner receives the funds.

The native profile uses one BTC asset, an explicit signed owner surrender, and one trusted assessor's signed decision. Foreign voting and cooldown, time-based expiry and redemption windows, NFT operators, product pricing, NXM stake, commissions, reinsurance, MCR, and foreign loss adjudication are outside this bounded relation. Signed state events determine eligibility here. The initialized outpoint defines one pool lineage.

## Verification

The independent Integer reference is in `src/JetDiscovery/Ref/NexusMutual.hs`. It derives the next ledger, required authorization, funding and payout, and checks conservation for each continuing transition. The 24 accepting fixtures exercise both policy slots, both owners, combined solvency, concurrent deposits, all three assessment outcomes, transfers before redemption and deposit retrieval, exact payout, and terminal closure. The 39 rejection fixtures cover underfunding, wrong authority, withdrawal of encumbered funds, replay across claims and policy slots, mismatched state and payout, and duplicate redemption. The duplicate-input control uses two funded identical draw states of 3,000 sats each. Both provide the expected fee amount, and the transaction pays one refund. The control accepts at index 0 and rejects at index 1.

The driver is `tools/NexusMutualProbe.hs`. It verified the same CMR for prepared and canonical evaluation and observed prepared evaluation for every native vector. The canonical CMR is `0d63d38f55a050617444939d3083d565ae3e7ab08a122fec125a13f06bfdf1e2`. The native process used 5,346 MiB of RTS memory with an 8 GiB heap cap. The full freeze records 35 source files and the binary SHA-256 `94d83f6cb0507c5d56b1d82cd12b3ff1b6f1186c567b5717f10aa6ef2027d6a2`. Source hashes matched at completion. Fresh shared cost analysis follows corpus integration. [Native log](data/nexus-mutual-8g-native-verification.txt), [actual exit status](data/nexus-mutual-8g-full-status.json), [frozen provenance](data/nexus-mutual-8g-full-provenance.json).

| Check | Actual outcome | Wall seconds | Maximum live bytes |
| --- | --- | ---: | ---: |
| Independent Integer lifecycle | PASS, exit 0 | 0.35661 | 55,872 |
| Complete native program | **63/63 PASS, exit 0** | **121.31389** | **2,149,229,176** |

Build with the direct GHC/package flags in [CRYPTO-FAMILIES.md](CRYPTO-FAMILIES.md), then run:

```sh
python3 tools/run_crypto_validation.py --label FRESH-LABEL --binary BINARY \
  --build-dir BUILD-DIR --driver tools/NexusMutualProbe.hs --heap 8 \
  --group reference --group native --compiler-flags '-O1 -threaded -rtsopts -isrc'
```
