# Native UMA optimistic bond lifecycle

`app-uma-optimistic-bond-lifecycle` implements one initialized assertion
lineage. The asserter posts a BTC bond, the designated challenger can post
one equal counterbond, and the state then pays either the undisputed refund
or the adjudicated settlement. The native roles are fixed asserter, challenger,
arbitrator, Store and setup sponsor keys.

All 42 native vectors passed with one canonical CMR
`50cfa15d282af0d4f697974f279d1b8d1a78ae6a98aa890a662bf172f517136c`.
The run covered 11 accepted and 31 rejected transitions. All 41 independent
Store fee comparisons and all 11 linked wire and primitive checks passed.

The pinned source is `c8c3f67367afd1c767712a3dbe3c8cad01b9a4d8`.
`assertTruth`, `disputeAssertion`, and `settleAssertion` specify funding,
challenge and settlement. The constructor selects `0.5e18` as the default
burned bond percentage. The disputed payout computes the Store fee by
integer flooring that percentage of one bond and pays the remainder of both
bonds to the winner. The pinned source and its AGPL-3.0-only license are
retained as inert data with hashes in the contract source inventory.
[OptimisticOracleV3.sol](https://github.com/UMAprotocol/protocol/blob/c8c3f67367afd1c767712a3dbe3c8cad01b9a4d8/packages/core/contracts/optimistic-oracle-v3/implementation/OptimisticOracleV3.sol)

The native state commits its phase, bounded bond and assertion ID. The
initialization fixture supplies a pre-funded 10,000-sat setup carrier.
The profile accepts bonds from 2,000 to 1,000,000 sats. The minimum instantiates
the source's two-times-final-fee rule at a fixed 1,000-sat native final fee.
The maximum bounds the corpus profile. Both phases with bonded funds retain
the setup carrier as a separate accounting amount.

| Transition | Actual inputs in order | Actual outputs in order |
| --- | --- | --- |
| Assert | Setup state, asserter bond, 1,000-sat fee | Same leaf with carrier plus bond |
| Challenge once | Asserted state, equal challenger bond, 1,000-sat fee | Same leaf with carrier plus both bonds |
| Refund at CSV10 | Asserted state, 1,000-sat fee | Exact bond to asserter, carrier to setup sponsor |
| Resolve disputed | Challenged state, 1,000-sat fee | `2*bond - floor(bond/2)` to winner, `floor(bond/2)` to Store, carrier to setup sponsor |

The program checks actual current input index 0, distinct outpoints, exact
input count, current script and value, state opening, and empty Taproot path.
The bond input has the appropriate fixed role script and exact value. The
assertion and challenge each require the role's BIP340 signature over the
actual `sig_all_hash`. Each continuation commits the complete next state under
the same executable leaf and holds exactly the calculated value. Each
terminal path checks every output script and value and the exact output count.

The native assertion transcript is `SHA256_tagged(Assertion, claimDigest32
|| bondBE64 || setupHashRaw32 || setupIndexBE32)`. The claim digest is supplied
as a 32-byte field. Its domain and actual setup outpoint give the identifier
scope within the native lineage. The transaction primitive's raw hash bytes
are used directly. The application transcript encodes the numeric index as
big endian. The fixed arbitrator supplies the truth value and signs
`SHA256_tagged(Verdict, assertionID32 || outcomeByte || sig_all_hash32)`.
The outcome byte is 1 for true and 0 for false. This binds the claim, outcome
and actual Bitcoin transaction context, including the current outpoint.
State and action enter as one aggregate witness. All reuse comes from typed
projections and every successor is derived in the program.

The source enforces a timestamp expiry for new disputes. The native profile
uses CSV10 as a minimum coin age for the permissionless refund. The challenge
and refund spend the same asserted outpoint, so an authorized challenge can
still compete with a matured refund until one confirms. The fixtures exercise
both paths with the same assertion coin and block sequence 10. Bitcoin's
relative-lock consensus rules enforce the actual age. The test primitive view
checks sequence, type, version and the disable bit. Dispute truth is delegated
to the fixed arbitrator, while DVM voting, escalation settings, callback
delivery, Ethereum identity encoding and global registry behavior are outside
this single-lineage profile. [BIP68 relative lock rules](https://bips.dev/68/)

| Checked payout example | Winner, sats | Store, sats | Setup sponsor, sats |
| --- | ---: | ---: | ---: |
| Undisputed odd bond | 24,001 to asserter | | 10,000 |
| True verdict, 24,001-sat bond | 36,002 to asserter | 12,000 | 10,000 |
| False verdict, 24,001-sat bond | 36,002 to challenger | 12,000 | 10,000 |
| False verdict, 24,000-sat bond | 36,000 to challenger | 12,000 | 10,000 |

The independent Integer reference supplies the expected accounting and byte
transcripts. The diagnostic tests both verdicts, odd and even fee rounding,
both bond bounds, CSV boundaries, exact bond funding and independent fee inputs.
The adversarial vectors also change roles, replay a challenge, substitute a
claim identity or actual outpoint in a verdict, sign the opposite outcome,
and divert the winner, Store or carrier. Changed transactions receive fresh
authorization except where the attack intentionally reuses a signature.

The test setup and independent funding coins are synthetic. Every successor
spends the raw txid and output 0 of its actual preceding fixture. The driver
checks the no-witness network wire round trip and the actual C and Haskell
input and output primitives for all accepted fixtures. Ordinary Bitcoin
validation supplies input existence, authorization for the other inputs and
chain-age checks. The fixtures represent alternative spends of the same
lineage, with exact fee and value conservation within each candidate spend.

Build and run the bounded diagnostic from `jet-discovery/` with GHC 9.8.4.

```sh
ghc -O1 -w -threaded -rtsopts -isrc \
  -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery \
  -outputdir /private/tmp/uma-bond-build tools/UmaBondSmoke.hs \
  -o /private/tmp/uma-bond-smoke
python3 tools/run_uma_bond_vectors.py
```

The diagnostic driver uses `-O0` for the wide C/Haskell value comparisons.
The native kernel uses `-O1`. The run records hashes of the local source
closure, primary source inputs, executable and log.

The full run exited 0 with 138.421 seconds of RTS elapsed time at
`-N1 -A16m -M8G -s`. Maximum live residency was 1,894,531,112 bytes and total
RTS memory was 4,159 MiB. The source closure, primary inputs, executable and
log hashes all verified. The exact run and transcript are retained in
`reports/data/uma-bond-full42-8g-provenance.json` and
`reports/data/uma-bond-full42-8g-rts.txt`. The shared corpus runner supplies
the separate cost and budget analysis.
