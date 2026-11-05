# Bitcoin growth scope and count audit

The complete26-row scope inventory is [data/bitcoin-growth-scopes.tsv](data/bitcoin-growth-scopes.tsv), with immutable proposed ID, status, possible additional group count, exact primary source, complete predicate and independence gate. Its maximum columns describe conditional ceilings, never earned credit. URLs for metadata-only papers are copied from the original backlog; a paper title/abstract does not establish an implementation.

The first approved nine scopes include three applications already inside the104-group signed baseline. Their remaining ceiling is **five** additional groups: SilentPayment, BIP127, numeric DLC, BOLT12 and Ark refresh. Offered HTLC is useful extra coverage within the existing received-HTLC family when it changes only branch direction/constants. SilentPayment and BIP127 have complete same-CMR execution evidence and are frozen for integration; numeric DLC has a complete standard-wire implementation under actual Simplicity validation; BOLT12/Ark still have substantive work. No thirteen-group promise follows from these original nine scopes.

| Cohort | Rows | Current status | Conditional additional groups |
| --- | --- | --- | --- |
| First signed Bitcoin growth milestone | 3 | Integrated and already included in104 | 0 |
| Remaining originally approved full predicates | 5 | Two complete; one in validation; two in source review | At most5 |
| Offered HTLC mirror | 1 | Existing HTLC family | 0 |
| BIP47; combined BIP157/158; BIP152; bounded PSBT finalizer | 4 | Authorized for subsequent exact source review | At most4 |
| Public HD wallet payout; BOLT11 invoice; BOLT3 shachain justice; BOLT7 funding gossip | 4 | Parent-suggested independence/full-source audit | At most4 |
| BIP324 v2 established-session verifier | 1 | Substantial protocol/crypto feasibility gate | At most1 |
| Taproot Assets complete transfer client | 1 | Primary proof-spec/full-statement gate | At most1 |
| Stateless batch proof; Payment Trees; Sleepy; Elmo; Thora; Daric; Garrison | 7 | Full texts and distinct deployment predicates still not established here | At most7 |

These rows can cover at most22 additional groups beyond the104 baseline **only if every feasibility and independence gate passes**. The final two cohorts contain uncertain prospects and cannot be used as a credible claim that150 has already been reached or is assured. Combining the originally planned Bitcoin5, contract19 and crypto5 gives a133 ceiling before the later seventeen prospective Bitcoin scopes; target150 still needs17 distinct validated groups at that planning point.

Client verifiers are classified separately from enforceable onchain spend paths. BIP127 is intrinsically invalid virtual-transaction client verification. Numeric DLC checks a real standard P2WSH CET under an authenticated client UTXO/contract view. BOLT12 must use an explicitly client-supplied authenticated current UTC bound; transaction nLockTime does not prove present wall-clock time. A meaningful complete client predicate can receive one group, while its standalone parser/hash/signature helpers do not.

Current overlap rejections are deliberate. Existing PTLC claim/refund, CoinPool exit/deposit, generic revocation/to_local, assurance crowdfunding and colored-asset conservation cannot be recounted by adding a new protocol label. BIP327 KeyAgg/session assembly is already marked `upgrade_or_assembly_no_extra_count` in the backlog. The crypto agent audited WabiSabi's complete published paper and declined new public onchain credit: credential validation is private issuer/coordinator work, while its Bitcoin transaction is ordinary CoinJoin. Neither supplies an extra group here. A future watchtower or shachain application must authenticate the extra appointment/disclosure/justice relationships, and Taproot Assets must check its actual MS-SMT/split/Bitcoin anchor proofs rather than rename ordinary token conservation.

Later implementation will retain one structured witness per logical proof, projection-based reuse, actual wire/digest/output bindings, complete compatible source-vector inventories, fresh validly signed negative transactions, and exact per-vector canonical CMR evidence. Source-only rows remain unregistered and uncredited.
