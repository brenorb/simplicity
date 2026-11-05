# What counts as a separate corpus program

Every registered entry gets its own vectors, size, cost, selected-path
profile, ablations and candidate match rows. The 150-program gate uses
distinct groups in [corpus-classification.json](data/corpus-classification.json).
A program only contributes to the gate once its complete current vector set
passes. Full bounded spend conditions and full bounded verifiers are shown
separately from protocol components and kernels in
[coverage-and-costs.md](coverage-and-costs.md).

| Group | Separate measurements | Reason to count once |
| --- | --- | --- |
| CTV | `bip119-ctv-exact`, `bip119-ctv-native` | [Both constructions](../src/JetDiscovery/Corpus/Bip119Ctv.hs) commit to the same transaction fields. The byte-exact digest checks raw script preimages; the native alternative uses the transaction hashes already available in Simplicity. |
| CSFS | `bip348-csfs`, `bip348-csfs-32` | The second restricts message size and uses an existing fixed-message verification path. |
| P2MR construction | `bip360-p2mr-output`, `bip360-upstream-p2mr-output` | Two ways to construct and authenticate a bounded P2MR output, using a Simplicity leaf or a supplied published leaf opening. Neither executes a general P2MR spend. |
| HTLC | `app-htlc`, `app-htlc-hash160` | The same preimage-claim/timed-refund policy is measured with different hash encodings. |
| Stateless SHA-256 hash signatures | `pq-shrincs-stateless`, `pq-slh-dsa-sha2-128s` | The SHRINCS fallback and standard FIPS 205 baseline use the same FORS/hypertree verification construction. Their exact profiles and vectors are retained. |
| BLAKE2 compression | `xchain-blake2s-compress`, `xchain-blake2b-compress` | [One generator](../src/JetDiscovery/Corpus/Hashes.hs) specializes word width, IV, round count and rotations to each standard. Both retain their own data and candidate prices. |
| Unanimous fixed payout | `app-ark-forfeit`, `app-coinpool-close` | [Both bounded leaves](../src/JetDiscovery/Corpus/BitcoinExpansion.hs) require every named party's transaction signature and the exact fixed payout outputs. Party and output counts differ; the interactive protocol mechanisms are outside the leaves. |

A reusable arithmetic component and an application that uses it may have
different groups when the application enforces a separate state or spend
relation. For example, standalone TickMath computes a price for one tick.
The finite Uniswap V3 application also enforces exact swaps across a
committed tick boundary, positions, fee growth, and actual funded outputs.
That is a different predicate even though the same price convention informs
both measurements. The addition of a signature to a kernel alone does not
establish a distinct state application.

The final audit compares every exact measured CMR across group IDs. One
[disconnected sighash pair](DISCONNECTED-SIGHASH.md) has identical outer CMRs
but verified different disconnected-mode identities and different responses
to a changed transaction outpoint. Exact CMR equality is a useful check;
different CMRs alone do not prove semantic independence. The explicit group
map also reviews scopes and variants with different CMRs.
