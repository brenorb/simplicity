# Complete bounded numeric DLC CET client verifier

**Canonical byte order validated:** all15 actual Simplicity vectors and all15 raw-wire/Haskell/actual-C primitive checks pass with CMR `5ed86cc1fc06275d5e21e5d23df15677545798fae5754049d19ef140467365c0`. Native opHash is the raw32 wire/digest bytes; the program/reference use it directly. The untouched published BIP143 transaction roundtrips through the base serializer, the published ALL01 digest matches, and every parsed derived CET outpoint equals the original. At `-N1 -M8G -s`:200.807 seconds,3,235,232,016 maximum live bytes,6371MiB total RTS memory. Exact source/driver snapshots, binary/log and canonical fixture hashes are in `data/numeric-dlc-canonical-provenance.json` and `numeric-dlc-canonical-freeze/`.

The earlier result below is historical: its standard-wire compatibility claim and CMR were withdrawn because a local reversed-opHash parser was compensated by program/reference reversals. Original logs, snapshots and signed Growth2 fixtures remain unchanged; current complete CET bytes are `bitcoin-growth3/numeric-dlc-derived-canonical-cet.hex`. See `OUTPOINT-BYTEORDER.md`.

`app-numeric-dlc-adaptor-cet` implements a standard Bitcoin P2WSH2of2 Contract Execution Transaction (CET) verifier. It checks actual oracle digit relations, both actual ECDSA adaptor signatures and their decrypted low-S ECDSAs on the exact actual BIP143 ALL01 transaction digest. It is a client verifier under an authenticated funding/contract/oracle-announcement view, not a Simplicity leaf controlling the original P2WSH output. It receives one application group; its arithmetic, DLEQ, oracle and codec helpers receive none.

Primary algorithms are the DLC specification contributors' [Oracle](https://github.com/discreetlogcontracts/dlcspecs/blob/9cd9148938c616690c79d99ec6f330e213c246c5/Oracle.md), [Numeric Outcome Compression](https://github.com/discreetlogcontracts/dlcspecs/blob/9cd9148938c616690c79d99ec6f330e213c246c5/NumericOutcomeCompression.md), [ECDSA adaptor](https://github.com/discreetlogcontracts/dlcspecs/blob/9cd9148938c616690c79d99ec6f330e213c246c5/ECDSA-adaptor.md) and [Transaction](https://github.com/discreetlogcontracts/dlcspecs/blob/9cd9148938c616690c79d99ec6f330e213c246c5/Transactions.md) documents. Source revision `9cd9148938c616690c79d99ec6f330e213c246c5`, attribution and CC-BY4.0 license are retained in the original growth packet. Numeric Outcome DLCs credits Nadav Kohen. [BIP143](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0143.mediawiki), by Johnson Lau and Pieter Wuille, is public domain. These implementations are new bounded Haskell/Simplicity expressions, not downloaded executable code.

The committed contract has two unsigned decimal digits, distinct fixed per-digit oracle nonces, and one oracle key. Each digit uses the exact `DLC/oracle/attestation/v0` UTF-8 message hash and BIP340 challenge; the program verifies the revealed scalar against the independently derived signature point. It sums the two points/scalars, rejects zero/infinity and uses that aggregate as the adaptor encryption point/decryption key. It supports every00..99 outcome without interval compression, rounding, signed outcomes or multiple oracles.

The actual funding UTXO is one committed outpoint/index0,102000 satoshis, with the lexicographically sorted compressed2of2 P2WSH script. The CET must have version2, nLockTime900000, sequenceFFFFFFFE, empty scriptSig, no annex and exactly two committed P2WPKH payout scripts in negotiated serial-ID order. PayoutA is `(outcome+1)*1000`; payoutB is `101000-payoutA`. Both remain at or above the specification's1000-satoshi dust bound; funding includes a1000-satoshi closing fee. No input amount, funding outpoint, script, output amount or digest is accepted merely because the proof supplies it.

For each party, the program checks the exact tagged `DLEQ` proof over `(R_a,Y,R,A_G,A_Y)` and the ECDSA encrypted-signature relation `s_a^-1(mG+rX)=R_a`. It computes low-S decryption from the actual checked oracle scalar sum and independently runs the full ECDSA verifier on the resulting `(r,s)` and actual CET digest. All proof points/scalars are canonical, points are on curve, and required points/scalars are nonzero. The complete proof enters through one structured `witness`; all reuse flows through projections. `numericKernel` is a zero-Witness `Assert+Primitive` kernel used by `boundProgram`.

The byte/Integer reference serializes the complete standard Segwit CET witness, including both actual low-S DER+ALL signatures, the CHECKMULTISIG dummy and the exact witnessScript. The local parser roundtrips that actual wire; both final ECDSAs verify. `bitcoin-growth3/numeric-dlc-derived-canonical-cet.hex` and `.tsv` retain the current canonical derived fixture. The older Growth2 files remain historical. Actual authenticated chain-view acquisition, oracle-announcement verification, funding creation, nonce/key setup, refund negotiation and the complete offchain DLC exchange remain external client/protocol boundaries. This is not proof that the synthetic funding outpoint exists on a live chain.

| Complete Simplicity vector | Expected / actual |
| --- | --- |
| Outcome42, both genuine oracle scalars and both ECDSA adaptors | Accept / Accept |
| Lower endpoint00 | Accept / Accept |
| Upper endpoint99 | Accept / Accept |
| Fresh valid adaptors for wrong negotiated payout | Reject / Reject |
| Fresh valid adaptors for diverted payout script | Reject / Reject |
| Fresh valid adaptors for changed maturity | Reject / Reject |
| Fresh valid adaptors with final sequence disabling maturity | Reject / Reject |
| Fresh valid adaptors for substituted funding outpoint | Reject / Reject |
| Oracle scalar changed at its single occurrence | Reject / Reject |
| Nondecimal digit10 | Reject / Reject |
| Oracle scalar n | Reject / Reject |
| Adaptor proof challenge changed at its single occurrence | Reject / Reject |
| Noncanonical DLEQ challenge n | Reject / Reject |
| Noncanonical DLEQ response n | Reject / Reject |
| Noncanonical encrypted response s_a=n | Reject / Reject |

Historical pre-correction run: all15 jetted Haskell Simplicity evaluations passed, with the whole-program CMR checked per vector by the prepared runner: `fb10a8e7bb6a2d86fc5ac254bf4f6a03c542ec36480b442f160e827ddcb800fc`. GHC9.8.4 `-O1`, `-N1 -M8G -s`:189.762 seconds elapsed, max live3,230,743,280 bytes, total RTS memory6363MiB. Exact module/runner snapshots, driver/data hashes, executable hash and log hash are in `data/numeric-dlc-provenance.json`. No shared full-corpus cost result is claimed here. Two earlier3G-capped attempts exhausted the heap during CMR construction and are preserved as failures; neither supplies a successful result.

All11 published ECDSA adaptor JSON rows are inventoried and exercised by the independent reference:3verification,3recovery and5serialization cases, including bad proof, R/r mismatch, high-S recovery, curve x above group order, zero response and out-of-range response. All pass their upstream expectations. The complete13 named BIP143 inline digest cases are inventoried; one exact published one-input ALL01 six-of-six message independently cross-checks the reference digest. The other BIP143 modes/code-separator examples are not claimed as complete CET vectors. No official complete two-digit CET packet was published in the pinned source; whole-application transactions are explicitly derived.

Reproduction: `tools/extract_dlc_adaptor_vectors.py`, `NumericDlcReference.hs` and `NumericDlcSmoke.hs`; source `Lib.NumericDlc` and `Ref.NumericDlc`. No shared registry/Cabal integration is performed by these standalone tools.

A standalone reproduction can compile the frozen source tree against the cached package database: `ghc -O1 -threaded -rtsopts -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery -ireports/data/numeric-dlc-canonical-freeze/src -outputdir /tmp/numeric-repro reports/data/numeric-dlc-canonical-freeze/tools/NumericDlcSmoke.hs -o /tmp/numeric-repro-run`, then `/tmp/numeric-repro-run +RTS -N1 -M8G -s`. `runVectors` checks each vector's type/kernel fingerprint/canonical composition CMR before actual evaluation. Preparation avoids repeated inference and does not accept a changed proof-input type or changed kernel.
