# Candidate: `keccak_f1600` — Keccak-f[1600] permutation

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Strong**: One permutation matches 12 distinct groups and changes fixed-stack fit in 11 budget-applicable programs. FairSwap falls from 93,362.551 to 1,343.255 WU at the estimate. Benchmark the reusable permutation for hash, bridge, permit, oracle and compressed asset paths before bundling address recovery.

Price: **1.530 WU (ESTIMATE)**. 2 x Sha256Block: software Keccak-f[1600] takes roughly twice a SHA-256 compression

Matches in 12 of 157 registered rows: 12 matched DAG nodes across all branches, 94 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| xchain-keccak256 | kernel | 1 | 1 | 5,775.502 | 24.296 | 5,751.206 | no / yes at 2283 WU |
| crypto-shake256-xof | kernel | 5 | 1 | 48,583.398 | 19,827.368 | 28,756.030 | no / yes at 35673 WU |
| xchain-eip712-permit | protocol_component | 4 | 1 | 24,042.559 | 1,037.735 | 23,004.824 | no / yes at 6170 WU |
| xchain-wormhole-13-of-19 | native_full_verifier | 21 | 1 | 128,724.783 | 7,949.457 | 120,775.326 | no / no at 5955 WU |
| xchain-ecrecover | native_full_verifier | 1 | 1 | 6,147.718 | 396.512 | 5,751.206 | no / yes at 3734 WU |
| xchain-keccak-merkle-membership | protocol_component | 4 | 1 | 23,783.769 | 778.945 | 23,004.824 | no / yes at 3458 WU |
| app-sealed-bid-auction-escrow | native_full_spend | 1 | 1 | 6,910.538 | 1,159.332 | 5,751.206 | no / yes at 6531 WU |
| app-permit2-bitmap-transfer | native_full_spend | 6 | 1 | 37,217.352 | 2,710.116 | 34,507.236 | no / yes at 10154 WU |
| app-compressed-asset-transfer | native_full_spend | 8 | 1 | 48,300.329 | 2,290.681 | 46,009.648 | no / yes at 6396 WU |
| app-vaa-bridge-replay-payout | native_full_spend | 22 | 1 | 136,523.527 | 9,996.995 | 126,526.532 | no / yes at 12721 WU |
| app-ocr-report-state-machine | native_full_spend | 5 | 1 | 31,208.149 | 2,452.119 | 28,756.030 | no / yes at 8566 WU |
| app-fairswap-file-sale | native_full_spend | 16 | 1 | 93,362.551 | 1,343.255 | 92,019.296 | no / yes at 4206 WU |

See the [complete matrix](../../reports/candidate-ranking.md#keccak_f1600) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`Vector32 Word64 -> Vector32 Word64` (25 lanes used)

## Specification
`JetDiscovery.Corpus.Hashes.keccakF`: 24 rounds of theta, rho, pi, chi, iota; passes the Keccak-256 known answers for "" and "abc".

## Cost (ESTIMATE)
ESTIMATE: 2 x `Sha256Block` = 1.530 WU. Software Keccak-f[1600] takes roughly twice a SHA-256 compression without hardware acceleration.

## Generality
Primitive for Ethereum interoperability (Keccak-256 addresses, storage proofs, bridge light clients), SHA-3/SHAKE (FIPS 202) and some STARK hash choices.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium to high. It is a new permutation, but a regular one: fixed rounds of 64-bit xor/and/not/rotate. The 64-bit word-jet proofs and the symbolic-execution approach used for SHA-256 apply; the state is large (1600 bits).

## Alternatives considered
Compose the existing 64-bit word jets for all 24 permutation rounds.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
