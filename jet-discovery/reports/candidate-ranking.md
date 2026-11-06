# Current candidate ranking evidence

All hypothetical prices, overlays, savings and scores are **ESTIMATE**. Original expression bounds are measured. This is a complete isolated-scenario matrix, not a combination of candidate savings.

sum of positive isolated bound savings per deduplicated program group, weighted by execution context, times generality divided by burden. Savings already include static occurrences; do not multiply by occurrences again.

For each candidate family and count_group choose the largest positive isolated saving among variants/frontends; report all individual rows separately. This is a conservative alternative envelope, not a composed overlay.

Context weights are explicit judgement: {"client": 0.1, "kernel": 0.1, "native_full_spend": 1, "native_full_verifier": 0.5, "protocol_component": 0.25}. Static occurrences already affect each measured bound difference; multiplying by occurrences again would double-count that benefit.

| rank | family | tier | matched groups | saving groups | saving groups with zero selected occurrences | selected occurrences in scored rows | native WU saved ESTIMATE | client WU saved ESTIMATE | component/kernel WU saved ESTIMATE | weighted score | generality / burden |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | p256_fe_multiply | maybe | 2 | 2 | 0 | 17422 | 18,466,901.872 | 0.000 | 0.000 | 9,233,450.936 | 2 / 3 |
| 2 | multiply_256 | maybe | 10 | 10 | 0 | 35689 | 2,686,725.360 | 0.000 | 57,044.960 | 2,526,395.964 | 3 / 2 |
| 3 | m31_mul | strong | 5 | 5 | 0 | 81154 | 815,666.528 | 0.000 | 986.174 | 815,863.763 | 2 / 1 |
| 4 | ed25519_fe_multiply | maybe | 1 | 1 | 0 | 5835 | 2,358,810.420 | 0.000 | 0.000 | 786,270.140 | 2 / 3 |
| 5 | qm31_mul | strong | 3 | 3 | 0 | 5068 | 1,215,718.416 | 0.000 | 479.952 | 607,907.203 | 2 / 2 |
| 6 | div_mod_256 | strong | 7 | 7 | 0 | 148 | 224,710.537 | 0.000 | 2,643.724 | 337,462.364 | 3 / 2 |
| 7 | keccak_f1600 | strong | 12 | 12 | 0 | 94 | 460,096.480 | 0.000 | 80,516.884 | 308,839.762 | 3 / 4 |
| 8 | sha256_wots_chain_16 | strong | 2 | 2 | 0 | 277 | 256,129.098 | 0.000 | 0.000 | 192,096.824 | 3 / 2 |
| 9 | multiply_128 | maybe | 18 | 18 | 0 | 2828 | 36,096.336 | 0.000 | 8,597.376 | 110,488.925 | 3 / 1 |
| 10 | ecrecover | maybe | 6 | 6 | 0 | 43 | 253,547.574 | 0.000 | 6,036.847 | 97,344.158 | 2 / 4 |
| 11 | div_mod_512 | maybe | 8 | 8 | 0 | 141 | 26,012.420 | 0.000 | 497,952.040 | 68,375.504 | 3 / 3 |
| 12 | sha512_compress | strong | 4 | 4 | 0 | 18 | 27,181.845 | 65,236.428 | 5,436.369 | 47,296.410 | 3 / 2 |
| 13 | sha256_pair | maybe | 7 | 7 | 0 | 7202 | 29,744.260 | 0.000 | 0.000 | 44,833.215 | 3 / 1 |
| 14 | blake3_compress_cv | maybe | 1 | 1 | 0 | 33 | 0.000 | 0.000 | 129,060.855 | 12,906.086 | 2 / 2 |
| 15 | ripemd160_compress | maybe | 5 | 5 | 0 | 5 | 4,910.840 | 4,910.840 | 2,455.420 | 8,471.199 | 3 / 2 |
| 16 | koalabear_add | maybe | 1 | 1 | 0 | 1884 | 0.000 | 0.000 | 6,382.992 | 1,276.598 | 2 / 1 |
| 17 | bn254_fp_multiply | maybe | 2 | 2 | 0 | 4 | 0.000 | 0.000 | 15,202.440 | 760.122 | 2 / 4 |
| 18 | blake2b_compress | rejected | 1 | 1 | 0 | 1 | 0.000 | 0.000 | 4,630.337 | 694.551 | 3 / 2 |
| 19 | blake2s_compress | rejected | 1 | 1 | 0 | 1 | 0.000 | 0.000 | 3,252.438 | 487.866 | 3 / 2 |
| 20 | signature_unpack | maybe | 1 | 1 | 0 | 1 | 213.702 | 0.000 | 0.000 | 320.553 | 3 / 1 |
| 21 | secp256k1_ecdsa_verify | maybe | 3 | 3 | 0 | 7 | 148.161 | 888.966 | 0.000 | 162.977 | 3 / 3 |
| 22 | pubkey_unpack_neg | maybe | 1 | 1 | 0 | 1 | 106.653 | 0.000 | 0.000 | 159.980 | 3 / 1 |

## Every candidate and program

The tables retain every program row, including off-path matches and negative savings. Matched DAG nodes include all branches and count each shared node once. Selected occurrences use the worst path after repricing; a different branch can become the bound, leaving zero selected occurrences and a positive saving. Feasibility uses the first-vector fixed hypothetical witness budget capped by the in-tree maximum. Client rows are inapplicable. No candidate has an assigned consensus encoding.

## `koalabear_add`

[Specification, C/proof burden and alternatives](../candidates/koalabear_add/README.md).

Price: 0.179WU **ESTIMATE**. ESTIMATE: Add32 plus Subtract32 benchmark analogues for exact wrap-add and one conditional subtraction, q=2130706433; no C implementation/benchmark

Exact32-bit wrap-add/single-subtract helper in published/deployed KoalaBear16 Poseidon2, with total noncanonical-word semantics. C needs add/subtract/select; existing32-bit carry/borrow proof patterns apply. Current demand is one component family, not a new full application. Tier: maybe. The exact wrap-and-reduce helper gives a meaningful saving in one deployed-source Poseidon2 component and has a small proof burden. More application evidence is needed before prioritizing a prime-specific add.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 1884 | 1 | 10,947.177 | 4,564.185 | 6,382.992 | no / yes |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `bn254_fp_multiply`

[Specification, C/proof burden and alternatives](../candidates/bn254_fp_multiply/README.md).

Price: 1.626WU **ESTIMATE**. ESTIMATE: 2 x FeMultiply for a generic 254-bit Montgomery reduction; requires an implementation and benchmark

Generic254-bit reduction supports Groth16/BitVM arithmetic; new prime/reduction proof. Tier: maybe. The measured base- and extension-field kernels show substantial local savings and a plausible BitVM proof path. Benchmark canonical input and output conversion before valuing a pairing verifier; only the dense multiplication component is modeled.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 1 | 1 | 3,867.295 | 66.685 | 3,800.610 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 3 | 1 | 11,821.680 | 419.850 | 11,401.830 | no / yes |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `secp256k1_ecdsa_verify`

[Specification, C/proof burden and alternatives](../candidates/secp256k1_ecdsa_verify/README.md).

Price: 94.293WU **ESTIMATE**. Sum of ScalarInvert, LinearCombination1, GejNormalize, GeIsOnCurve and ScalarNormalize benchmark analogues. This ESTIMATE omits two separate scalar multiplications and range/control overhead.

Known-key external signatures; existing group/scalar lemmas, new ECDSA equivalence. Tier: maybe. Known-key ECDSA can reuse existing curve proofs. The corpus separates client signatures and native predicates, and the current price omits two scalar multiplications and range/control work. Benchmark exact affine and scalar checks first.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 2 | 1 | 4,083.550 | 3,787.228 | 296.322 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 4 | 1 | 5,679.600 | 5,086.956 | 592.644 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 1 | 1 | 245.314 | 97.153 | 148.161 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `ecrecover`

[Specification, C/proof burden and alternatives](../candidates/ecrecover/README.md).

Price: 107.232WU **ESTIMATE**. ESTIMATE: existing secp256k1 operation benchmarks plus Keccak priced as 2 x Sha256Block

Ethereum-address identities; recovery uniqueness, affine encoding and Keccak proofs. Tier: maybe. The Ethereum-style bridge, permit and oracle paths benefit. In the quorum example the combined estimate with Keccak fits where either candidate alone does not. Benchmark reusable recovery to a point plus a separate permutation before fixing the Ethereum address and failure ABI.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 1 | 1 | 24,042.559 | 18,005.712 | 6,036.847 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 19 | 1 | 128,724.783 | 14,024.690 | 114,700.093 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 1 | 1 | 6,147.718 | 110.871 | 6,036.847 | no / yes |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 1 | 1 | 37,217.352 | 31,180.505 | 6,036.847 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 19 | 1 | 136,523.527 | 21,823.434 | 114,700.093 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 2 | 1 | 31,208.149 | 19,134.455 | 12,073.694 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `m31_mul`

[Specification, C/proof burden and alternatives](../candidates/m31_mul/README.md).

Price: 0.174WU **ESTIMATE**. 2 x FullMultiply32: one 32x32 multiply plus a Mersenne fold of similar cost

Small Mersenne-field multiplication with bounded folding proof. Tier: strong. The full STARK accounts for most savings, and the isolated M31 overlay does not make it fit the fixed-stack scenario. Benchmark this small reusable primitive alongside QM31 because the proof burden is smaller; compare the overlapping savings and exact raw-word contract.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 1 | 1 | 11.744 | 1.681 | 10.063 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 61 | 1 | 697.571 | 83.728 | 613.843 | no / yes |
| stark-qm31-mul / stark-qm31-mul | kernel | 16 | 1 | 245.781 | 84.773 | 161.008 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 20 | 1 | 346.899 | 145.639 | 201.260 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 81056 | 1 | 1,497,462.342 | 681,795.814 | 815,666.528 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `qm31_mul`

[Specification, C/proof burden and alternatives](../candidates/qm31_mul/README.md).

Price: 0.813WU **ESTIMATE**. FeMultiply: 16 small-limb products and reductions, comparable to a 10x26-bit-limb secp256k1 field multiply

Reusable degree4 extension multiplication; field-tower reduction proof. Tier: strong. The full STARK crosses the fixed-stack scenario by 5,001.074 WU at this estimated price. Benchmark the extension multiply and exact input domain; the margin is conditional and M31 savings overlap.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 1 | 1 | 245.781 | 5.805 | 239.976 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 1 | 1 | 346.899 | 106.923 | 239.976 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 5066 | 1 | 1,497,462.342 | 281,743.926 | 1,215,718.416 | no / yes |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `keccak_f1600`

[Specification, C/proof burden and alternatives](../candidates/keccak_f1600/README.md).

Price: 1.530WU **ESTIMATE**. 2 x Sha256Block: software Keccak-f[1600] takes roughly twice a SHA-256 compression

Reusable permutation across Ethereum commitments, bridge messages and SHAKE; new permutation proof. Tier: strong. One permutation matches 12 distinct groups and changes fixed-stack fit in 11 budget-applicable programs. FairSwap falls from 93,362.551 to 1,343.255 WU at the estimate. Benchmark the reusable permutation for hash, bridge, permit, oracle and compressed asset paths before bundling address recovery.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 1 | 1 | 5,775.502 | 24.296 | 5,751.206 | no / yes |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 5 | 1 | 48,583.398 | 19,827.368 | 28,756.030 | no / yes |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 4 | 1 | 24,042.559 | 1,037.735 | 23,004.824 | no / yes |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 21 | 1 | 128,724.783 | 7,949.457 | 120,775.326 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 1 | 1 | 6,147.718 | 396.512 | 5,751.206 | no / yes |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 4 | 1 | 23,783.769 | 778.945 | 23,004.824 | no / yes |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 1 | 1 | 6,910.538 | 1,159.332 | 5,751.206 | no / yes |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 6 | 1 | 37,217.352 | 2,710.116 | 34,507.236 | no / yes |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 8 | 1 | 48,300.329 | 2,290.681 | 46,009.648 | no / yes |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 22 | 1 | 136,523.527 | 9,996.995 | 126,526.532 | no / yes |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 5 | 1 | 31,208.149 | 2,452.119 | 28,756.030 | no / yes |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 16 | 1 | 93,362.551 | 1,343.255 | 92,019.296 | no / yes |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `blake3_compress_cv`

[Specification, C/proof burden and alternatives](../candidates/blake3_compress_cv/README.md).

Price: 0.535WU **ESTIMATE**. ESTIMATE: 7/10 of the BLAKE2s compression analogue (Sha256Block), scaled by 7 vs 10 rounds; no BLAKE3 C benchmark

Reusable BLAKE3 chaining and 256-bit root output; new seven-round schedule and feed-forward proof over established word operations. Tier: maybe. The bounded BitVM-style tree-hash component has substantial savings but remains one use family. Benchmark the raw CV/first-output-block ABI and compare it with smaller round helpers before proposing a jet.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 33 | 1 | 139,215.660 | 10,154.805 | 129,060.855 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `blake2s_compress`

[Specification, C/proof burden and alternatives](../candidates/blake2s_compress/README.md).

Price: 0.765WU **ESTIMATE**. Sha256Block: BLAKE2s compression and SHA-256 compression cost about the same in software

General32-bit compression; add/xor/rotate composition, new round proof. Tier: rejected. The exact fixed final-block frontend only matches its own kernel and shares one counting group with BLAKE2b. Broader rounds or common G helpers need a distinct exact reference and new evidence.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 1 | 1 | 3,256.768 | 4.330 | 3,252.438 | no / yes |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `blake2b_compress`

[Specification, C/proof burden and alternatives](../candidates/blake2b_compress/README.md).

Price: 1.147WU **ESTIMATE**. 1.5 x Sha256Block: BLAKE2b compresses 128 bytes with 64-bit words

General64-bit compression; add/xor/rotate composition, new round proof. Tier: rejected. The fixed twelve-round final-block prototype matches its own kernel. It does not cover the Ethereum variable-round/final-flag ABI; the current corpus does not justify prioritizing this specialized arrow.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 1 | 1 | 4,641.718 | 11.381 | 4,630.337 | no / yes |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `sha256_wots_chain_16`

[Specification, C/proof burden and alternatives](../candidates/sha256_wots_chain_16/README.md).

Price: 11.475WU **ESTIMATE**. 15 x Sha256Block for the matched 18-byte buffer alignment; a caller-profile ESTIMATE. An unrestricted valid context can require 30 compressions.

Generic bounded tweaked SHA256 chain, reusing compression correctness. Tier: strong. Prioritize the fixed-prefix frontend: both stateless variants cross their fixed-stack scenarios and share one counting group. The separate stateful group uses the generic frontend; its overlay prices the observed 18-byte buffer, and the unrestricted 30-compression path needs a separate price.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 32 | 1 | 15,175.556 | 8,335.428 | 6,840.128 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `sha256_wots_chain_16_fixed`

[Specification, C/proof burden and alternatives](../candidates/sha256_wots_chain_16_fixed/README.md).

Price: 11.475WU **ESTIMATE**. ESTIMATE: 15 x Sha256Block for the fixed 18-byte-address n16 chain frontend; same primitive family as sha256_wots_chain_16

Fixed-address frontend of the same tweaked SHA256 chain family; no extra family credit. Tier: strong. Prioritize the fixed-prefix frontend: both stateless variants cross their fixed-stack scenarios and share one counting group. The separate stateful group uses the generic frontend; its overlay prices the observed 18-byte buffer, and the unrestricted 30-compression path needs a separate price.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 175 | 1 | 198,670.811 | 20,607.261 | 178,063.550 | no / yes |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 245 | 1 | 275,877.127 | 26,588.157 | 249,288.970 | no / yes |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `sha256_pair`

[Specification, C/proof burden and alternatives](../candidates/sha256_pair/README.md).

Price: 1.530WU **ESTIMATE**. 2 x Sha256Block: SHA-256 of 64 bytes is two compressions

General two-block SHA256 helper; existing compression and padding proof patterns. Tier: maybe. A simple Merkle helper has several direct matches and a reusable proof path. Compare its smaller savings and the full verifier residual with existing two-compression composition before adding a separate fixed-size jet.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 16 | 1 | 242.966 | 176.886 | 66.080 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 4 | 1 | 442.566 | 426.046 | 16.520 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 4 | 1 | 372.067 | 355.547 | 16.520 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 8 | 1 | 522.699 | 489.659 | 33.040 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 2 | 1 | 408.583 | 400.323 | 8.260 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 1 | 1 | 1,294.901 | 1,290.771 | 4.130 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 7167 | 1 | 1,497,462.342 | 1,467,862.632 | 29,599.710 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `pubkey_unpack_neg`

[Specification, C/proof burden and alternatives](../candidates/pubkey_unpack_neg/README.md).

Price: 0.656WU **ESTIMATE**. FeNormalize analogue: one field-range check and a parity tag; the coordinate is returned unchanged

General canonical Schnorr key decode; range and field-negation proof. Tier: maybe. A cheap parser primitive with small isolated savings in variable-key CSFS. Existing complete Schnorr jets hide the parser in many other entries, so benchmark the paired parser use before prioritizing.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 1 | 1 | 408.282 | 301.629 | 106.653 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `signature_unpack`

[Specification, C/proof burden and alternatives](../candidates/signature_unpack/README.md).

Price: 1.156WU **ESTIMATE**. FeNormalize + ScalarNormalize: range checks on r and s

General canonical Schnorr signature decode; field/scalar range proofs. Tier: maybe. A small field/scalar range proof is attractive, but direct measured demand is concentrated in variable-message CSFS. Compare shared range checks and full Schnorr verification before selecting the frontend.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 1 | 1 | 408.282 | 194.580 | 213.702 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `div_mod_256`

[Specification, C/proof burden and alternatives](../candidates/div_mod_256/README.md).

Price: 0.676WU **ESTIMATE**. 4 x DivMod128_64, a limb-throughput ESTIMATE; it does not model every step of unrestricted 256-by-256 division.

Wide integer division across fixed-point/state accounting; total zero-divisor convention needs exact proof. Tier: strong. The estimate crosses the fixed-stack scenario for bounded Uniswap V3 (22,235.642 to 9,708.540 WU against 12,694) and LMSR (17,404.636 to 16,082.774 WU against 16,379). It also materially reduces Balancer and Pendle. Benchmark exact full-width and normalized narrow division separately: the limb proxy is incomplete.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 1 | 1 | 3,060.650 | 1,738.788 | 1,321.862 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 82 | 1 | 152,067.689 | 25,884.091 | 126,183.598 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 9 | 1 | 114,255.531 | 102,358.773 | 11,896.758 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 1 | 1 | 17,404.636 | 16,082.774 | 1,321.862 | no / yes |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 46 | 1 | 150,583.704 | 77,802.487 | 72,781.217 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 8 | 1 | 22,235.642 | 9,708.540 | 12,527.102 | no / yes |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 1 | 1 | 1,494.744 | 172.882 | 1,321.862 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `multiply_128`

[Specification, C/proof burden and alternatives](../candidates/multiply_128/README.md).

Price: 0.288WU **ESTIMATE**. 4 x Multiply64: four 64x64 products

General wide product with reusable limb carry proof. Tier: maybe. This small carry proof has exact matches across 18 groups. The isolated estimate crosses the LMSR scenario by only 191.272 WU; larger savings in some pool predicates leave substantial residuals. Benchmark it against composition from existing Multiply64.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 4 | 1 | 3,838.308 | 3,775.092 | 63.216 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 12 | 1 | 10,060,198.439 | 10,060,008.791 | 189.648 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 4 | 1 | 2,925,636.828 | 2,925,573.612 | 63.216 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 2 | 1 | 3,060.650 | 3,029.042 | 31.608 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 512 | 1 | 514,052.014 | 505,960.366 | 8,091.648 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 4 | 1 | 3,813.287 | 3,750.071 | 63.216 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 12 | 1 | 10,063,358.661 | 10,063,169.013 | 189.648 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 1536 | 1 | 218,376.473 | 194,101.529 | 24,274.944 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 288 | 1 | 152,067.689 | 147,516.137 | 4,551.552 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 35 | 1 | 114,255.531 | 113,702.391 | 553.140 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 77 | 1 | 17,404.636 | 16,187.728 | 1,216.908 | no / yes |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 265 | 1 | 150,583.704 | 146,395.644 | 4,188.060 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 48 | 1 | 22,235.642 | 21,477.050 | 758.592 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 6 | 1 | 2,288.682 | 2,193.858 | 94.824 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 4 | 1 | 3,867.295 | 3,804.079 | 63.216 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 12 | 1 | 11,821.680 | 11,632.032 | 189.648 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 6 | 1 | 1,494.744 | 1,399.920 | 94.824 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 1 | 1 | 138.722 | 122.918 | 15.804 | yes / yes |

## `multiply_256`

[Specification, C/proof burden and alternatives](../candidates/multiply_256/README.md).

Price: 1.152WU **ESTIMATE**. 16 x Multiply64: sixteen 64x64 products (schoolbook 256x256)

General wide product with expanded limb carry proof. Tier: maybe. The regular wide product matches ten groups; the largest savings are concentrated in Ed25519 and P-256, which remain above their fixed-stack scenarios. Compare generic limb arithmetic against dedicated reductions before selecting a width.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 3 | 1 | 3,838.308 | 3,607.668 | 230.640 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 8720 | 1 | 10,060,198.439 | 9,389,804.839 | 670,393.600 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 17507 | 1 | 2,925,636.828 | 1,579,698.668 | 1,345,938.160 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 20 | 1 | 3,060.650 | 1,523.050 | 1,537.600 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 608 | 1 | 514,052.014 | 467,308.974 | 46,743.040 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 3 | 1 | 3,813.287 | 3,582.647 | 230.640 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 96 | 1 | 22,775.359 | 15,394.879 | 7,380.480 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 8720 | 1 | 10,063,358.661 | 9,392,965.061 | 670,393.600 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 3 | 1 | 3,867.295 | 3,636.655 | 230.640 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 9 | 1 | 11,821.680 | 11,129.760 | 691.920 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `div_mod_512`

[Specification, C/proof burden and alternatives](../candidates/div_mod_512/README.md).

Price: 2.704WU **ESTIMATE**. 16 x DivMod128_64, a 512-by-256 proxy ESTIMATE; the exact prototype accepts a full 512-bit divisor.

Large division and quotient/remainder proof; wide state and zero-divisor convention. Tier: maybe. The bounded Curve invariant still costs 38,396.334 WU against its 5,206-WU scenario; the full StableSwap pool has no exact match. The only fit change is in the BN254 Fp2 kernel. Benchmark unrestricted and normalized division separately; the 512-by-256 price proxy is incomplete.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 1 | 1 | 3,838.308 | 122.248 | 3,716.060 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 3 | 1 | 10,060,198.439 | 10,049,050.259 | 11,148.180 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 1 | 1 | 2,925,636.828 | 2,921,920.768 | 3,716.060 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 128 | 1 | 514,052.014 | 38,396.334 | 475,655.680 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 1 | 1 | 3,813.287 | 97.227 | 3,716.060 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 3 | 1 | 10,063,358.661 | 10,052,210.481 | 11,148.180 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 1 | 1 | 3,867.295 | 151.235 | 3,716.060 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 3 | 1 | 11,821.680 | 673.500 | 11,148.180 | no / yes |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `ripemd160_compress`

[Specification, C/proof burden and alternatives](../candidates/ripemd160_compress/README.md).

Price: 0.765WU **ESTIMATE**. Sha256Block: RIPEMD-160 and SHA-256 compression cost about the same in software

Bitcoin HASH160 interoperability; new dual-lane compression proof. Tier: maybe. Several Bitcoin HASH160 and interoperability paths match the same compression. Verify whether a compression jet changes spend fit often enough to justify the new dual-lane proof alongside the broader SHA candidates.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 1 | 1 | 2,469.559 | 14.139 | 2,455.420 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 1 | 1 | 2,546.490 | 91.070 | 2,455.420 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 1 | 1 | 4,296.691 | 1,841.271 | 2,455.420 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 1 | 1 | 5,897.705 | 3,442.285 | 2,455.420 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 1 | 1 | 69,731.129 | 67,275.709 | 2,455.420 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `sha512_compress`

[Specification, C/proof burden and alternatives](../candidates/sha512_compress/README.md).

Price: 1.147WU **ESTIMATE**. 1.5 x Sha256Block: SHA-512 compresses 128 bytes with 64-bit words (as blake2b_compress)

General hash/HMAC/Ed25519 workload;64-bit SHA2 schedule proof. Tier: strong. The estimate brings the native BIP32 withdrawal below its fixed-stack scenario. The same compression is useful in HMAC, Ed25519 and BIP47 client work, which is reported separately. Benchmark the reusable block primitive.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 1 | 1 | 5,454.166 | 17.797 | 5,436.369 | no / yes |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 1 | 1 | 2,925,636.828 | 2,920,200.459 | 5,436.369 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 12 | 1 | 69,731.129 | 4,494.701 | 65,236.428 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 4 | 1 | 22,481.299 | 735.823 | 21,745.476 | no / yes |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `p256_fe_multiply`

[Specification, C/proof burden and alternatives](../candidates/p256_fe_multiply/README.md).

Price: 1.219WU **ESTIMATE**. 1.5 x FeMultiply: a P-256 field multiply with Solinas reduction is somewhat slower than libsecp256k1's

Non-native curve arithmetic; P256 Solinas reduction proof and canonical field contract. Tier: maybe. Dedicated reduction saves 9,233,450.936 WU in each of the two P-256-based predicates. Residual estimates of 826,747.503 WU for standalone verification and 829,907.725 WU for WebAuthn still exceed their 13,272- and 19,725-WU fixed-stack scenarios. Benchmark the field ABI and compare a reusable curve-level verifier.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 8711 | 1 | 10,060,198.439 | 826,747.503 | 9,233,450.936 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 0 | 0 | 2,925,636.828 | 2,925,636.828 | 0.000 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 8711 | 1 | 10,063,358.661 | 829,907.725 | 9,233,450.936 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

## `ed25519_fe_multiply`

[Specification, C/proof burden and alternatives](../candidates/ed25519_fe_multiply/README.md).

Price: 0.813WU **ESTIMATE**. FeMultiply: 2^255-19 reduction is as cheap as secp256k1's (fold by 38)

Non-native curve arithmetic;25519 reduction proof and canonical field contract. Tier: maybe. Large savings in one interoperability verifier still leave a substantial residual. Benchmark raw field reduction and compare the dedicated curve and SHA-512 pieces before pursuing this as a broadly demanded jet.

| program / count group | scope | selected occurrences | matched DAG nodes | current WU | isolated WU ESTIMATE | WU saved ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-p2pk-sigall / baseline-p2pk-sigall | native_full_spend | 0 | 0 | 54.348 | 54.348 | 0.000 | yes / yes |
| bip348-csfs / bip348-csfs | native_full_verifier | 0 | 0 | 408.282 | 408.282 | 0.000 | yes / yes |
| bip348-csfs-32 / bip348-csfs | native_full_verifier | 0 | 0 | 51.769 | 51.769 | 0.000 | yes / yes |
| bip119-ctv-exact / bip119-ctv-exact | protocol_component | 0 | 0 | 3,737.013 | 3,737.013 | 0.000 | no / no |
| bip119-ctv-native / bip119-ctv-exact | protocol_component | 0 | 0 | 37.720 | 37.720 | 0.000 | yes / yes |
| bip446-templatehash-exact / bip446-templatehash-exact | protocol_component | 0 | 0 | 1,937.968 | 1,937.968 | 0.000 | no / no |
| bip448-lnsymmetry-update / bip448-lnsymmetry-update | native_full_spend | 0 | 0 | 1,988.048 | 1,988.048 | 0.000 | no / no |
| bip346-txhash / bip346-txhash | protocol_component | 0 | 0 | 2,662.929 | 2,662.929 | 0.000 | yes / yes |
| bip347-op-cat / bip347-op-cat | protocol_component | 0 | 0 | 8,793.377 | 8,793.377 | 0.000 | no / no |
| bip118-apo / bip118-apo | native_full_spend | 0 | 0 | 88.451 | 88.451 | 0.000 | yes / yes |
| bip349-internalkey / bip349-internalkey | native_full_spend | 0 | 0 | 54.216 | 54.216 | 0.000 | yes / yes |
| bip442-paircommit / bip442-paircommit | kernel | 0 | 0 | 136.837 | 136.837 | 0.000 | yes / yes |
| bip443-ccv-output / bip443-ccv-output | protocol_component | 0 | 0 | 183.741 | 183.741 | 0.000 | yes / yes |
| bip116-merklebranchverify / bip116-merklebranchverify | protocol_component | 0 | 0 | 145.685 | 145.685 | 0.000 | yes / yes |
| bip117-tail-call / bip117-tail-call | native_full_spend | 0 | 0 | 54.153 | 54.153 | 0.000 | yes / yes |
| bip360-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 50.266 | 50.266 | 0.000 | yes / yes |
| bip441-bignum-modmul / bip441-bignum-modmul | kernel | 0 | 0 | 3,838.308 | 3,838.308 | 0.000 | yes / yes |
| bip449-tweakadd / bip449-tweakadd | kernel | 0 | 0 | 196.394 | 196.394 | 0.000 | yes / yes |
| tluv-remove-leaf / tluv-remove-leaf | protocol_component | 0 | 0 | 193.342 | 193.342 | 0.000 | yes / yes |
| app-htlc / app-htlc | native_full_spend | 0 | 0 | 62.340 | 62.340 | 0.000 | yes / yes |
| app-multisig-2of3 / app-multisig-2of3 | native_full_spend | 0 | 0 | 165.825 | 165.825 | 0.000 | yes / yes |
| app-vault / app-vault | native_full_spend | 0 | 0 | 130.351 | 130.351 | 0.000 | yes / yes |
| app-dlc-cfd / app-dlc-cfd | native_full_spend | 0 | 0 | 116.885 | 116.885 | 0.000 | yes / yes |
| app-merkle-key / app-merkle-key | native_full_spend | 0 | 0 | 242.966 | 242.966 | 0.000 | yes / yes |
| xchain-ripemd160 / xchain-ripemd160 | kernel | 0 | 0 | 2,469.559 | 2,469.559 | 0.000 | yes / yes |
| app-htlc-hash160 / app-htlc | native_full_spend | 0 | 0 | 2,546.490 | 2,546.490 | 0.000 | yes / yes |
| bip443-ccv-aggregate / bip443-ccv-aggregate | protocol_component | 0 | 0 | 345.320 | 345.320 | 0.000 | yes / yes |
| app-vault-batch-recover / app-vault-batch-recover | native_full_spend | 0 | 0 | 171.348 | 171.348 | 0.000 | yes / yes |
| pq-shrincs-stateful / pq-shrincs-stateful | native_full_verifier | 0 | 0 | 15,175.556 | 15,175.556 | 0.000 | no / no |
| pq-shrincs-stateless / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 198,670.811 | 198,670.811 | 0.000 | no / no |
| pq-slh-dsa-sha2-128s / pq-shrincs-stateless | native_full_verifier | 0 | 0 | 275,877.127 | 275,877.127 | 0.000 | no / no |
| xchain-blake2s-compress / xchain-blake2-compression | kernel | 0 | 0 | 3,256.768 | 3,256.768 | 0.000 | no / no |
| xchain-blake2b-compress / xchain-blake2-compression | kernel | 0 | 0 | 4,641.718 | 4,641.718 | 0.000 | no / no |
| xchain-keccak256 / xchain-keccak256 | kernel | 0 | 0 | 5,775.502 | 5,775.502 | 0.000 | no / no |
| xchain-p256-ecdsa / xchain-p256-ecdsa | native_full_verifier | 0 | 0 | 10,060,198.439 | 10,060,198.439 | 0.000 | no / no |
| xchain-sha512 / xchain-sha512 | kernel | 0 | 0 | 5,454.166 | 5,454.166 | 0.000 | no / no |
| xchain-ed25519 / xchain-ed25519 | native_full_verifier | 5835 | 1 | 2,925,636.828 | 566,826.408 | 2,358,810.420 | no / no |
| stark-m31-mul / stark-m31-mul | kernel | 0 | 0 | 11.744 | 11.744 | 0.000 | yes / yes |
| stark-m31-inv / stark-m31-inv | kernel | 0 | 0 | 697.571 | 697.571 | 0.000 | no / no |
| stark-qm31-mul / stark-qm31-mul | kernel | 0 | 0 | 245.781 | 245.781 | 0.000 | yes / yes |
| stark-fri-fold / stark-fri-fold | kernel | 0 | 0 | 346.899 | 346.899 | 0.000 | yes / yes |
| app-symmetric-channel-state / app-symmetric-channel-state | native_full_spend | 0 | 0 | 436.864 | 436.864 | 0.000 | yes / yes |
| app-refillable-withdrawal-budget / app-refillable-withdrawal-budget | native_full_spend | 0 | 0 | 362.614 | 362.614 | 0.000 | yes / yes |
| app-owner-authenticated-storage / app-owner-authenticated-storage | native_full_spend | 0 | 0 | 331.494 | 331.494 | 0.000 | yes / yes |
| app-merkle-sum-reserve-keeper / app-merkle-sum-reserve-keeper | native_full_spend | 0 | 0 | 351.250 | 351.250 | 0.000 | yes / yes |
| app-noninteractive-fee-bump / app-noninteractive-fee-bump | native_full_spend | 0 | 0 | 138.918 | 138.918 | 0.000 | yes / yes |
| app-hodl-price-vault / app-hodl-price-vault | native_full_spend | 0 | 0 | 117.523 | 117.523 | 0.000 | yes / yes |
| app-point-time-locked-payment / app-point-time-locked-payment | native_full_spend | 0 | 0 | 153.863 | 153.863 | 0.000 | yes / yes |
| app-payjoin-proposal-bounds / app-payjoin-proposal-bounds | native_full_spend | 0 | 0 | 159.211 | 159.211 | 0.000 | yes / yes |
| app-assurance-crowdfunding / app-assurance-crowdfunding | native_full_spend | 0 | 0 | 269.746 | 269.746 | 0.000 | yes / yes |
| app-payment-pool-merkle-exit / app-payment-pool-merkle-exit | native_full_spend | 0 | 0 | 442.566 | 442.566 | 0.000 | yes / yes |
| app-payment-pool-funded-deposit / app-payment-pool-funded-deposit | native_full_spend | 0 | 0 | 372.067 | 372.067 | 0.000 | yes / yes |
| app-payment-pool-internal-transfer / app-payment-pool-internal-transfer | native_full_spend | 0 | 0 | 522.699 | 522.699 | 0.000 | yes / yes |
| app-merkle-distributor-bitmap / app-merkle-distributor-bitmap | native_full_spend | 0 | 0 | 408.583 | 408.583 | 0.000 | yes / yes |
| app-native-state-counter / app-native-state-counter | native_full_spend | 0 | 0 | 282.572 | 282.572 | 0.000 | yes / yes |
| pq-lms-sha256-m32-h10 / pq-lms-sha256-m32-h10 | native_full_verifier | 0 | 0 | 90,875.147 | 90,875.147 | 0.000 | no / no |
| app-perpetual-funding-settlement / app-perpetual-funding-settlement | native_full_spend | 0 | 0 | 939.871 | 939.871 | 0.000 | yes / yes |
| app-median-oracle-settlement / app-median-oracle-settlement | native_full_spend | 0 | 0 | 252.265 | 252.265 | 0.000 | yes / yes |
| app-conditional-collateral-redemption / app-conditional-collateral-redemption | native_full_spend | 0 | 0 | 923.487 | 923.487 | 0.000 | yes / yes |
| app-royalty-payment-splitter / app-royalty-payment-splitter | native_full_spend | 0 | 0 | 1,701.086 | 1,701.086 | 0.000 | yes / yes |
| xchain-uniswap-v3-tick-math / xchain-uniswap-v3-tick-math | kernel | 0 | 0 | 3,060.650 | 3,060.650 | 0.000 | yes / yes |
| xchain-curve-stableswap-invariant / xchain-curve-stableswap-invariant | kernel | 0 | 0 | 514,052.014 | 514,052.014 | 0.000 | no / no |
| xchain-fullmath-muldiv / xchain-fullmath-muldiv | kernel | 0 | 0 | 3,813.287 | 3,813.287 | 0.000 | yes / yes |
| bip360-upstream-p2mr-output / bip360-construction | protocol_component | 0 | 0 | 110.087 | 110.087 | 0.000 | yes / yes |
| pq-xmss-sha2-10-256 / pq-xmss-sha2-10-256 | native_full_verifier | 0 | 0 | 67,400.513 | 67,400.513 | 0.000 | no / no |
| app-lightning-to-local / app-lightning-to-local | native_full_spend | 0 | 0 | 66.360 | 66.360 | 0.000 | yes / yes |
| app-lightning-anchor / app-lightning-anchor | native_full_spend | 0 | 0 | 59.915 | 59.915 | 0.000 | yes / yes |
| app-lightning-received-htlc / app-lightning-received-htlc | native_full_spend | 0 | 0 | 136.478 | 136.478 | 0.000 | yes / yes |
| app-inheritance / app-inheritance | native_full_spend | 0 | 0 | 187.021 | 187.021 | 0.000 | yes / yes |
| app-decaying-multisig / app-decaying-multisig | native_full_spend | 0 | 0 | 192.550 | 192.550 | 0.000 | yes / yes |
| app-statechain-recovery / app-statechain-recovery | native_full_spend | 0 | 0 | 118.052 | 118.052 | 0.000 | yes / yes |
| app-ark-unilateral-exit / app-ark-unilateral-exit | native_full_spend | 0 | 0 | 78.056 | 78.056 | 0.000 | yes / yes |
| app-ark-forfeit / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 127.526 | 127.526 | 0.000 | yes / yes |
| app-coinpool-close / app-unanimous-fixed-payout | native_full_spend | 0 | 0 | 205.496 | 205.496 | 0.000 | yes / yes |
| app-dlc-enumerated / app-dlc-enumerated | native_full_spend | 0 | 0 | 79.727 | 79.727 | 0.000 | yes / yes |
| app-arbitrated-escrow / app-arbitrated-escrow | native_full_spend | 0 | 0 | 142.688 | 142.688 | 0.000 | yes / yes |
| app-fidelity-bond / app-fidelity-bond | native_full_spend | 0 | 0 | 60.902 | 60.902 | 0.000 | yes / yes |
| app-reserve-preserving-spend / app-reserve-preserving-spend | native_full_spend | 0 | 0 | 71.909 | 71.909 | 0.000 | yes / yes |
| app-babylon-unbonding / app-babylon-unbonding | native_full_spend | 0 | 0 | 254.287 | 254.287 | 0.000 | yes / yes |
| app-babylon-slashing / app-babylon-slashing | native_full_spend | 0 | 0 | 318.123 | 318.123 | 0.000 | yes / yes |
| app-recurring-payment / app-recurring-payment | native_full_spend | 0 | 0 | 80.576 | 80.576 | 0.000 | yes / yes |
| app-op-evict-complete / app-op-evict-complete | native_full_spend | 0 | 0 | 495.451 | 495.451 | 0.000 | yes / yes |
| app-bip322-message-control-proof / app-bip322-message-control-proof | native_full_spend | 0 | 0 | 296.114 | 296.114 | 0.000 | yes / yes |
| app-bitcoin-spv-payment-receipt / app-bitcoin-spv-payment-receipt | native_full_spend | 0 | 0 | 1,294.901 | 1,294.901 | 0.000 | yes / yes |
| app-silent-payment-output-covenant / app-silent-payment-output-covenant | native_full_spend | 0 | 0 | 4,296.691 | 4,296.691 | 0.000 | yes / yes |
| app-reserve-ownership-and-sum / app-reserve-ownership-and-sum | client | 0 | 0 | 673.110 | 673.110 | 0.000 | n/a (client) |
| app-numeric-dlc-adaptor-cet / app-numeric-dlc-adaptor-cet | client | 0 | 0 | 4,083.550 | 4,083.550 | 0.000 | n/a (client) |
| app-bolt12-invoice-authorization / app-bolt12-invoice-authorization | client | 0 | 0 | 2,668.522 | 2,668.522 | 0.000 | n/a (client) |
| app-ark-round-refresh / app-ark-round-refresh | client | 0 | 0 | 5,897.705 | 5,897.705 | 0.000 | n/a (client) |
| app-bip157-158-filter-query / app-bip157-158-filter-query | client | 0 | 0 | 199,955.368 | 199,955.368 | 0.000 | n/a (client) |
| app-bip152-compact-block-reconstruction / app-bip152-compact-block-reconstruction | client | 0 | 0 | 4,757.113 | 4,757.113 | 0.000 | n/a (client) |
| app-bip47-notification-payment-client / app-bip47-notification-payment-client | client | 0 | 0 | 69,731.129 | 69,731.129 | 0.000 | n/a (client) |
| app-bip174-mixed-psbt-finalizer-extractor / app-bip174-mixed-psbt-finalizer-extractor | client | 0 | 0 | 5,679.600 | 5,679.600 | 0.000 | n/a (client) |
| app-bip32-public-hd-withdrawal / app-bip32-public-hd-withdrawal | native_full_spend | 0 | 0 | 22,481.299 | 22,481.299 | 0.000 | no / no |
| crypto-siphash24 / crypto-siphash24 | kernel | 0 | 0 | 4,265.816 | 4,265.816 | 0.000 | no / no |
| crypto-chacha20-block / crypto-chacha20-block | kernel | 0 | 0 | 2,258.812 | 2,258.812 | 0.000 | no / no |
| crypto-poly1305 / crypto-poly1305 | kernel | 0 | 0 | 22,775.359 | 22,775.359 | 0.000 | no / no |
| app-webauthn-counter-wallet / app-webauthn-counter-wallet | native_full_spend | 0 | 0 | 10,063,358.661 | 10,063,358.661 | 0.000 | no / no |
| crypto-poseidon2-koalabear16 / crypto-poseidon2-koalabear16 | kernel | 0 | 0 | 10,947.177 | 10,947.177 | 0.000 | no / no |
| crypto-blake3-tree-hash / crypto-blake3-tree-hash | kernel | 0 | 0 | 139,215.660 | 139,215.660 | 0.000 | no / no |
| crypto-shake256-xof / crypto-shake256-xof | kernel | 0 | 0 | 48,583.398 | 48,583.398 | 0.000 | no / no |
| crypto-ml-dsa-ntt256 / crypto-ml-dsa-ntt256 | kernel | 0 | 0 | 13,236.906 | 13,236.906 | 0.000 | yes / yes |
| op-civ-linked-input / op-civ-linked-input | native_full_spend | 0 | 0 | 9.085 | 9.085 | 0.000 | yes / yes |
| op-inout-amount-withdrawal-cap / op-inout-amount-withdrawal-cap | protocol_component | 0 | 0 | 9.011 | 9.011 | 0.000 | yes / yes |
| draft64-signed-widening-multiply / draft64-signed-widening-multiply | kernel | 0 | 0 | 20.824 | 20.824 | 0.000 | yes / yes |
| stark-fibonacci-full / stark-fibonacci-full | native_full_verifier | 0 | 0 | 1,497,462.342 | 1,497,462.342 | 0.000 | no / no |
| xchain-eip712-permit / xchain-eip712-permit | protocol_component | 0 | 0 | 24,042.559 | 24,042.559 | 0.000 | no / no |
| xchain-wormhole-13-of-19 / xchain-wormhole-13-of-19 | native_full_verifier | 0 | 0 | 128,724.783 | 128,724.783 | 0.000 | no / no |
| xchain-secp256k1-ecdsa / xchain-secp256k1-ecdsa | native_full_verifier | 0 | 0 | 245.314 | 245.314 | 0.000 | yes / yes |
| xchain-ecrecover / xchain-ecrecover | native_full_verifier | 0 | 0 | 6,147.718 | 6,147.718 | 0.000 | no / no |
| xchain-keccak-merkle-membership / xchain-keccak-merkle-membership | protocol_component | 0 | 0 | 23,783.769 | 23,783.769 | 0.000 | no / no |
| app-tokenized-native-vault / app-tokenized-native-vault | native_full_spend | 0 | 0 | 2,479.128 | 2,479.128 | 0.000 | yes / yes |
| app-asynchronous-vault-claims / app-asynchronous-vault-claims | native_full_spend | 0 | 0 | 2,440.844 | 2,440.844 | 0.000 | yes / yes |
| app-ascending-auction-escrow / app-ascending-auction-escrow | native_full_spend | 0 | 0 | 754.767 | 754.767 | 0.000 | yes / yes |
| app-sealed-bid-auction-escrow / app-sealed-bid-auction-escrow | native_full_spend | 0 | 0 | 6,910.538 | 6,910.538 | 0.000 | no / no |
| app-squads-proposal-execution / app-squads-proposal-execution | native_full_spend | 0 | 0 | 952.865 | 952.865 | 0.000 | yes / yes |
| app-cumulative-payment-splitter / app-cumulative-payment-splitter | native_full_spend | 0 | 0 | 572.173 | 572.173 | 0.000 | yes / yes |
| app-sablier-cancelable-cliff-stream / app-sablier-cancelable-cliff-stream | native_full_spend | 0 | 0 | 829.112 | 829.112 | 0.000 | yes / yes |
| app-uma-optimistic-bond-lifecycle / app-uma-optimistic-bond-lifecycle | native_full_spend | 0 | 0 | 731.599 | 731.599 | 0.000 | yes / yes |
| app-budgeted-quadratic-funding / app-budgeted-quadratic-funding | native_full_spend | 0 | 0 | 662.992 | 662.992 | 0.000 | yes / yes |
| app-oz-delegated-snapshot-governance / app-oz-delegated-snapshot-governance | native_full_spend | 0 | 0 | 1,190.217 | 1,190.217 | 0.000 | yes / yes |
| app-uniswap-v2-fee-on-pool / app-uniswap-v2-fee-on-pool | native_full_spend | 0 | 0 | 157,358.814 | 157,358.814 | 0.000 | no / no |
| app-native-mutual-insurance / app-native-mutual-insurance | native_full_spend | 0 | 0 | 878.718 | 878.718 | 0.000 | yes / yes |
| app-maker-clipper-partial-liquidation / app-maker-clipper-partial-liquidation | native_full_spend | 0 | 0 | 1,213.245 | 1,213.245 | 0.000 | yes / yes |
| app-permit2-bitmap-transfer / app-permit2-bitmap-transfer | native_full_spend | 0 | 0 | 37,217.352 | 37,217.352 | 0.000 | no / no |
| app-compressed-asset-transfer / app-compressed-asset-transfer | native_full_spend | 0 | 0 | 48,300.329 | 48,300.329 | 0.000 | no / no |
| app-vaa-bridge-replay-payout / app-vaa-bridge-replay-payout | native_full_spend | 0 | 0 | 136,523.527 | 136,523.527 | 0.000 | no / no |
| app-conditional-position-partitions / app-conditional-position-partitions | native_full_spend | 0 | 0 | 4,138.384 | 4,138.384 | 0.000 | yes / yes |
| app-interest-accruing-loan-rollover / app-interest-accruing-loan-rollover | native_full_spend | 0 | 0 | 5,554.868 | 5,554.868 | 0.000 | yes / yes |
| app-ocr-report-state-machine / app-ocr-report-state-machine | native_full_spend | 0 | 0 | 31,208.149 | 31,208.149 | 0.000 | no / no |
| app-batch-limit-order-settlement / app-batch-limit-order-settlement | native_full_spend | 0 | 0 | 7,328.241 | 7,328.241 | 0.000 | yes / yes |
| app-stableswap-pool-transition / app-stableswap-pool-transition | native_full_spend | 0 | 0 | 218,376.473 | 218,376.473 | 0.000 | no / no |
| app-weighted-pool-transition / app-weighted-pool-transition | native_full_spend | 0 | 0 | 152,067.689 | 152,067.689 | 0.000 | no / no |
| app-proactive-market-maker-private-pool / app-proactive-market-maker-private-pool | native_full_spend | 0 | 0 | 114,255.531 | 114,255.531 | 0.000 | no / no |
| app-lmsr-prediction-market / app-lmsr-prediction-market | native_full_spend | 0 | 0 | 17,404.636 | 17,404.636 | 0.000 | no / no |
| app-pendle-term-market-transition / app-pendle-term-market-transition | native_full_spend | 0 | 0 | 150,583.704 | 150,583.704 | 0.000 | no / no |
| app-concentrated-pool-swap / app-concentrated-pool-swap | native_full_spend | 0 | 0 | 22,235.642 | 22,235.642 | 0.000 | no / no |
| app-cryptoswap-transition / app-cryptoswap-transition | native_full_spend | 0 | 0 | 37,834.493 | 37,834.493 | 0.000 | no / no |
| app-virtual-reserve-launch / app-virtual-reserve-launch | native_full_spend | 0 | 0 | 779.711 | 779.711 | 0.000 | yes / yes |
| app-lido-fifo-withdrawal-queue / app-lido-fifo-withdrawal-queue | native_full_spend | 0 | 0 | 2,288.682 | 2,288.682 | 0.000 | yes / yes |
| eprint-lamport-transaction-signature / eprint-lamport-transaction-signature | native_full_verifier | 0 | 0 | 2,485.800 | 2,485.800 | 0.000 | yes / yes |
| eprint-bitvm-nand-dispute / eprint-bitvm-nand-dispute | protocol_component | 0 | 0 | 32.778 | 32.778 | 0.000 | yes / yes |
| eprint-bitvm-equivocation-slash / eprint-bitvm-equivocation-slash | protocol_component | 0 | 0 | 16.662 | 16.662 | 0.000 | yes / yes |
| eprint-blind-schnorr-response / eprint-blind-schnorr-response | protocol_component | 0 | 0 | 1,189.997 | 1,189.997 | 0.000 | no / no |
| eprint-frost-signature-share / eprint-frost-signature-share | protocol_component | 0 | 0 | 587.039 | 587.039 | 0.000 | yes / yes |
| app-fairswap-file-sale / app-fairswap-file-sale | native_full_spend | 0 | 0 | 93,362.551 | 93,362.551 | 0.000 | no / no |
| eprint-bn254-fp-multiply / eprint-bn254-fp-multiply | kernel | 0 | 0 | 3,867.295 | 3,867.295 | 0.000 | yes / yes |
| eprint-bn254-fp2-multiply / eprint-bn254-fp2-multiply | kernel | 0 | 0 | 11,821.680 | 11,821.680 | 0.000 | no / no |
| xchain-uniswap-v2-amount-out / xchain-uniswap-v2-amount-out | kernel | 0 | 0 | 1,494.744 | 1,494.744 | 0.000 | yes / yes |
| eprint-adaptor-sig / eprint-adaptor-sig | native_full_verifier | 0 | 0 | 407.577 | 407.577 | 0.000 | yes / yes |
| eprint-musig2-keyagg / eprint-musig2-keyagg | protocol_component | 0 | 0 | 902.028 | 902.028 | 0.000 | yes / yes |
| eprint-ring-sig / eprint-ring-sig | native_full_verifier | 0 | 0 | 1,246.504 | 1,246.504 | 0.000 | no / no |
| eprint-dleq-cashu / eprint-dleq-cashu | native_full_verifier | 0 | 0 | 635.639 | 635.639 | 0.000 | yes / yes |
| ethsol-linear-vesting / ethsol-linear-vesting | native_full_spend | 0 | 0 | 77.632 | 77.632 | 0.000 | yes / yes |
| ethsol-dutch-auction / ethsol-dutch-auction | native_full_spend | 0 | 0 | 45.666 | 45.666 | 0.000 | yes / yes |
| ethsol-safe-allowance / ethsol-safe-allowance | native_full_spend | 0 | 0 | 287.365 | 287.365 | 0.000 | yes / yes |
| ethsol-lending-liquidation / ethsol-lending-liquidation | native_full_spend | 0 | 0 | 138.722 | 138.722 | 0.000 | yes / yes |

