# Witness dataflow audit of the contract/application expansion

Simplicity witness values are not committed by CMR. Two Haskell expressions
`witness x` do not impose equality on the two published witness nodes, even if
honest fixtures fill them with the same value. A spender can unshare the nodes,
supply different values, and preserve the program CMR. This was a defect in the
corpus construction, not a disagreement in upstream Simplicity semantics.

The corrected construction materializes each logical witness once and passes
it through a witness-free kernel. Repeated projections and `iden` reuse the
actual input value. Conditional paths retain that input with `iden`; they do
not discard it and recreate the fields from new witness nodes.

## Repaired programs

| module | affected program IDs | previous alias-sensitive boundary | repair |
| --- | --- | --- | --- |
| ContractExpansion | `xchain-eip712-permit` | nonce check, typed-data digest and signature could use different copies of permit fields | one `(fields,signature)` witness before `permitAuthT` |
| FinancialApps | `app-perpetual-funding-settlement` | signed funding index, allowed range and payout arithmetic | one `(index,signature)` witness before `fundingT` |
| FinancialApps | `app-median-oracle-settlement` | authenticated observations and median/payout calculation | one observations-plus-three-signatures witness before `medianOracleT` |
| FinancialApps | `app-conditional-collateral-redemption` | authenticated weights, normalization and proportional payouts | one weights-plus-signature witness before `conditionalT` |
| StatefulApps | `app-payment-pool-merkle-exit` | authenticated old root, member key/balance, successor root and payout | one proof-plus-signature witness before `poolExitT` |
| StatefulApps | `app-payment-pool-funded-deposit` | old empty leaf, deposit positivity, credited root and funded output | one proof-plus-amount witness before `poolDepositT` |
| StatefulApps | `app-payment-pool-internal-transfer` | sender authorization/debit and receiver/intermediate-root update | one two-proofs/amount/signature witness before `poolTransferT` |
| StatefulApps | `app-merkle-distributor-bitmap` | eligibility proof, claimed-bit check, successor bitmap and beneficiary payout | one bitmap-plus-proof witness before `couponT` |
| StatefulApps | `app-native-state-counter` | old-state authentication and counter increment | one state witness before `counterT` |
| ProposalApps | `app-hodl-price-vault` | oracle-authenticated price/height and threshold checks | one report-plus-two-signatures witness before `hodlT` |
| ProposalApps | `app-assurance-crowdfunding` | data-committed refund key, signature key and refund destination | one owner-plus-branch-signature witness before `crowdfundT` |
| StateMachines | `app-symmetric-channel-state` | authenticated old state, signed successor, version/conservation checks and continuation | one mode/old/new/signatures witness before `channelT` |
| StateMachines | `app-refillable-withdrawal-budget` | old budget/nonce, arithmetic, signatures and successor state | one mode/state/amount/signature witness before `budgetT` |
| StateMachines | `app-merkle-sum-reserve-keeper` | committed liability root and input/output solvency thresholds | one proof-plus-signature witness before `reserveT` |

All sixteen `BitcoinExpansion` policies also now consume one fixed typed witness
containing mode, secret and eight optional signature slots. Previously, their
repeated free branch selectors selected a union of independently guarded paths,
and signatures were validated within each selected slot; no cross-copy identity
was needed for that union. The rewrite removes the repeated nodes anyway.

`app-owner-authenticated-storage` previously used each independent old/new/signature
operand once; it now uses one aggregate witness before `ownerStoreT` as well.
`Lib.State` contains no witness constructors and accepts projected inputs.

The ECDSA/ecrecover kernels and all three `ContractMath` kernels already consumed
an actual input, so their internal range/curve/arithmetic checks share that input.
The Keccak membership path now consumes each sibling hash and ordering bit
together in one per-level witness before its pure ordering/hash kernel. The
previous use of committed sibling constants prevented general proof variation; a
changed-sibling negative now checks rejection without changing the CMR.
Wormhole consumed its body once and each optional guardian signature once,
validating each slot against its own constant guardian address. The royalty
splitter has no witnesses. NIFB/payjoin each consume one signature, and PTLC
consumes its entire branch payload once before `match`.

## Executed same-CMR attack regression

`Regression/WitnessState.hs` reproduces the previous counter defect against the
actual Bitcoin evaluator (`jetSubst`, then `fastEval` in a real `PrimEnv`). A UTXO
commits state41 and the proposed continuation also contains41:

| check | observed result |
| --- | --- |
| CMR of legacy `(loaded=41,computed=41)` equals legacy `(loaded=41,computed=40)` | true |
| Consistent legacy witness rejects the frozen continuation | true |
| Split legacy witness accepts the frozen continuation at that exact same CMR | true |
| Actual repaired `StatefulApps.counter 41` rejects the frozen continuation | true |
| Actual repaired `StatefulApps.counter 40` rejects the forged old-state witness | true |

The unsafe expression exists only in this regression; it is never registered in
the corpus. The repaired counter is the actual exported corpus implementation.

Reproduction from `jet-discovery/`, after `cabal build lib:jet-discovery` inside
its Nix shell (the package-db path uses the pinned GHC9.8.4 toolchain):

```sh
mkdir -p /tmp/jet-discovery-contract-audit
nix-shell --run 'ghc -O0 -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery -odir /tmp/jet-discovery-contract-audit -hidir /tmp/jet-discovery-contract-audit src/JetDiscovery/Regression/WitnessState.hs tools/CheckWitnessState.hs -o /tmp/jet-discovery-contract-audit/check-witness-state && /tmp/jet-discovery-contract-audit/check-witness-state'
```

The normal library build passed after these repairs. The additional state-machine
and regression modules passed an isolated `ghc -fno-code` check. The focused
`tools/CheckContractVectors.hs` run completed every vector of all42 expansion entries:
**42 groups,202 vectors,zero failed groups**. The first16 BitcoinExpansion groups
completed63 vectors; the resumed `remaining` run completed26 groups/139 vectors
and exited0. Its final output was `TOTAL: 26 groups, 139 vectors, 0 failed groups`.
The resumed run includes all five staged ContractExpansion groups/24 vectors,
all three ContractMath groups/20, FinancialApps4/23, StatefulApps5/24,
ProposalApps5/26 and StateMachines4/22. Every vector uses `Run.runVectors`, including
the per-witness CMR comparison and actual jet-substituted Bitcoin evaluator.
Cost/mining reports
must be regenerated after the repair: previously measured expressions and honest
vectors do not establish security against split-witness spends.

## Expression staging and honest cost modeling

After the dataflow repair, EIP712 stages its192-byte struct hash once before
constructing the exact66-byte `0x1901 || domain || structHash` envelope. Passing
an expensive hash expression separately to32 byte projections would execute that
hash32 times; sharing a Haskell expression or a DAG node does not cache its
result. The published bytes and hash formulas are unchanged. ECDSA verification
and recovery likewise compute their scalar inverse once before both products.
Their existing positive and negative vectors passed after this staging change.
No cost figures for the old redundant expressions should be used to justify a
candidate jet when ordinary value binding removes the redundant work.
