# Ethereum precompiles and Solana syscalls

These inventories record named runtime interfaces and the corresponding Bitcoin Simplicity evidence. Ethereum covers all 18 precompile addresses in the pinned Geth Ethereum mainnet fork map used for the study's November 4, 2026 UTC gas period. Solana covers all 44 named sBPF registrations at the pinned newer Agave revision and all 40 in the documented v3.1.8 release. The independent Solana cluster feature-activation state at the study's slot is unknown. No EVM gas or Solana compute units are converted to Simplicity WU. [Ethereum day coverage](ETHEREUM-DAY-GAS-RANKING.md), [Solana period coverage](PERIOD-RANKINGS.md), [source revisions, licenses and hashes](data/cross-ecosystem-interface-provenance.json).

## Ethereum mainnet

At Geth revision 78af8c3121686417cf8dee0f94e0e975f5b38a9e, the mainnet chainspec activates Prague on May 7, 2025 at 10:05:11 UTC and Osaka on December 3, 2025 at 21:49:11 UTC. The later recorded blob-parameter times do not select a different precompile map. The pinned mainnet configuration has no Amsterdam, Bogota or UBT activation in the study period. The implementation dispatch therefore selects the Osaka map for the complete November 4 UTC period. L2-specific contracts and hypothetical fork maps are outside this set. [Mainnet chainspec](https://github.com/ethereum/go-ethereum/blob/78af8c3121686417cf8dee0f94e0e975f5b38a9e/params/chainspecs/mainnet.json), [configuration and activation rules](https://github.com/ethereum/go-ethereum/blob/78af8c3121686417cf8dee0f94e0e975f5b38a9e/params/config.go), [Osaka map and fork dispatch](https://github.com/ethereum/go-ethereum/blob/78af8c3121686417cf8dee0f94e0e975f5b38a9e/core/vm/contracts.go#L150-L242), [complete registration TSV](data/ethereum-mainnet-precompile-registration.tsv).

| Address | Interface | Bitcoin Simplicity evidence and boundary |
| --- | --- | --- |
| 0x01 | ECRECOVER, secp256k1 | xchain-ecrecover measures address recovery from the typed inputs and uses a candidate exact expression. The EVM byte-buffer and failure-return ABI are outside that predicate. |
| 0x02 | SHA-256 | Existing SHA-256 compression and context jets cover bounded streaming computation. EVM input/gas handling is outside the scope. |
| 0x03 | RIPEMD-160 | xchain-ripemd160 measures a compression path and app-htlc-hash160 exercises the HASH160 interoperability use. Arbitrary-length EVM hashing is outside those bounds. |
| 0x04 | Identity | Existing identity and bounded typed composition. No new cryptographic primitive demand. |
| 0x05 | MODEXP | Wide multiply/divide and modular-arithmetic corpus kernels supply components. Variable-width input framing, exponentiation and Osaka length/gas rules are outside the measured relation. |
| 0x06 | BN254 G1 addition | The measured BN254 Fp/Fp2 kernels supply arithmetic only. Exact G1 addition and EVM point decoding remain open. |
| 0x07 | BN254 G1 scalar multiplication | Same field arithmetic components. Scalar action, point checks and the EVM ABI remain open. |
| 0x08 | BN254 pairing check | Fp/Fp2 measured and a dense arithmetic component extrapolated for the Groth16 bridge path. The pairing equation, subgroup checks and wire ABI remain open. [BN254 evidence](bn254-groth16.md). |
| 0x09 | BLAKE2f | xchain-blake2b-compress and its exact prototype fix 12 rounds and final-block flag. The complete EIP-152 interface lets the caller select rounds and final-block flag. [EIP-152](https://eips.ethereum.org/EIPS/eip-152). |
| 0x0a | KZG point evaluation | No corpus port. Versioned commitment handling, BLS12-381 points and the pairing equation are distinct from the measured M31 STARK. [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844). |
| 0x0b | BLS12-381 G1 addition | No corpus port. Needs the BLS12-381 field, point representation and exact validation. |
| 0x0c | BLS12-381 G1 MSM | No corpus port. Needs the G1 group, scalar and batch semantics. |
| 0x0d | BLS12-381 G2 addition | No corpus port. Needs the BLS12-381 extension field, G2 representation and exact validation. |
| 0x0e | BLS12-381 G2 MSM | No corpus port. Needs the G2 group, scalar and batch semantics. |
| 0x0f | BLS12-381 pairing check | No corpus port. BN254 arithmetic and its dense estimate use a different curve and proof relation. |
| 0x10 | BLS12-381 Fp-to-G1 map | No corpus port. Requires this curve's specified map and clearing behavior. |
| 0x11 | BLS12-381 Fp2-to-G2 map | No corpus port. Requires the corresponding extension-field map and clearing behavior. |
| 0x100 | P256VERIFY, secp256r1 | xchain-p256-ecdsa measures ECDSA with checked inverse hints. app-webauthn-counter-wallet applies that relation to a Bitcoin wallet. Exact EVM ABI, return convention and EIP-7951 vector coverage are outside the measured entries. |

The seven BLS12-381 interfaces are specified together by EIP-2537. RIP-7212 remains a relevant L2 source for the P-256 verifier. Ethereum mainnet uses EIP-7951, which specifies the infinity rejection and modular x comparison. Keccak-256 is also a relevant Ethereum demand signal through the EVM instruction and hashed application data, outside the precompile map. xchain-keccak256 and the Keccak-based contract verifiers measure bounded applications of it. [EIP-2537](https://eips.ethereum.org/EIPS/eip-2537), [RIP-7212](https://github.com/ethereum/RIPs/blob/master/RIPS/rip-7212.md), [EIP-7951](https://eips.ethereum.org/EIPS/eip-7951), [Ethereum opcode reference](https://ethereum.org/en/developers/docs/evm/opcodes/).

## Solana sBPF runtime

The 40 symbols in the Foundation's pinned syscall reference match the complete registration set of Agave v3.1.8 at 2717084afeeb7baad4342468c27f528ef617a3cf. Its separate reserved v2 loader in that source has no registration calls. The newer pinned Agave revision 84ca856dc20c509a6140c7b4310fa60c209feaaf keeps all 40 symbols and adds sol_sha512, sol_curve_decompress, sol_curve_pairing_map and sol_invoke_signed_v2. The exact source conditions for both snapshots are in the table. “Direct” means the registration call in that source is unconditional. Implementations may separately gate operation IDs, validate their environment or charge compute. Neither snapshot independently identifies the program binary or activated feature accounts at the study's specific slot. [Foundation reference at 48e5554d](https://github.com/solana-foundation/solana-com/blob/48e5554dc6547c95c4167ef6226119d79fe4cd86/apps/docs/content/docs/en/core/programs/syscall-reference.mdx), [v3.1.8 registration](https://github.com/anza-xyz/agave/blob/2717084afeeb7baad4342468c27f528ef617a3cf/syscalls/src/lib.rs#L282-L537), [newer registration](https://github.com/anza-xyz/agave/blob/84ca856dc20c509a6140c7b4310fa60c209feaaf/syscalls/src/lib.rs#L313-L529), [complete two-revision TSV](data/agave-syscall-registration.tsv).


| Symbol | Newer Agave registration | v3.1.8 registration | Bitcoin Simplicity mapping |
| --- | --- | --- | --- |
| `abort` | Direct | Direct | Runtime termination and diagnostics. Simplicity assertions can fail. The host diagnostics interface has no Bitcoin mapping. |
| `sol_panic_` | Direct | Direct | Runtime termination and diagnostics. Simplicity assertions can fail. The host diagnostics interface has no Bitcoin mapping. |
| `sol_log_` | Direct | Direct | SVM logging and observability. No Bitcoin spending predicate. |
| `sol_log_64_` | Direct | Direct | SVM logging and observability. No Bitcoin spending predicate. |
| `sol_log_pubkey` | Direct | Direct | SVM logging and observability. No Bitcoin spending predicate. |
| `sol_log_compute_units_` | Direct | Direct | SVM logging and observability. No Bitcoin spending predicate. |
| `sol_create_program_address` | Direct | Direct | Account derivation with an Ed25519 off-curve test and optional bump search. Taproot state-key derivation is a different relation. |
| `sol_try_find_program_address` | Direct | Direct | Account derivation with an Ed25519 off-curve test and optional bump search. Taproot state-key derivation is a different relation. |
| `sol_sha256` | Direct | Direct | Existing SHA-256 block/context jets. Bounded composition covers hashing. The SBF slice ABI remains outside scope. |
| `sol_keccak256` | Direct | Direct | xchain-keccak256 and Keccak contract programs cover bounded hashing. SHAKE also uses the permutation under different framing. |
| `sol_secp256k1_recover` | Direct | Direct | xchain-ecrecover supplies related recovery arithmetic and returns an Ethereum address. The SBF syscall returns a public key and accepts its own recovery IDs and ABI. |
| `sol_blake3` | `blake3_syscall_enabled` | `blake3_syscall_enabled` | crypto-blake3-tree-hash implements a bounded unkeyed tree hash. blake3_compress_cv is its exact compression frontend. The SBF slice ABI is outside scope. |
| `sol_sha512` | `enable_sha512_syscall` | Absent | xchain-sha512 measures compression. Ed25519 and BIP32 HMAC applications provide related demand. The SBF slice ABI is outside scope. |
| `sol_curve_validate_point` | Direct | `curve25519_syscall_enabled` | The newer curve dispatch covers Edwards/Ristretto, BLS12-381 and gated secp256r1 variants. Ed25519 and P-256 verifiers check their own inputs. General point-validation ABI remains outside scope. |
| `sol_curve_group_op` | Direct | `curve25519_syscall_enabled` | Edwards/Ristretto, BLS12-381 and gated secp256r1 operations at the newer revision. Corpus signature verifiers supply related arithmetic. Generic group-op ABI remains outside scope. |
| `sol_curve_multiscalar_mul` | Direct | `curve25519_syscall_enabled` | Edwards/Ristretto and gated secp256r1 MSM at the newer revision. Existing Bitcoin secp256k1 linear-combination jets use a different curve. The exact SBF MSM relation is unimplemented. |
| `sol_curve_decompress` | Direct | Absent | The newer revision dispatches BLS12-381 G1/G2 and gated secp256r1. The exact SBF decompression relation is unimplemented. |
| `sol_curve_pairing_map` | Direct | Absent | The newer BLS12-381 operation returns a target-field element. BN254 component evidence uses a different curve. The pairing map is unimplemented. |
| `sol_get_clock_sysvar` | Direct | Direct | SVM cluster or account state. Bitcoin locktime and sequence predicates use transaction data. No direct Bitcoin runtime mapping. |
| `sol_get_epoch_schedule_sysvar` | Direct | Direct | SVM cluster or account state. Bitcoin locktime and sequence predicates use transaction data. No direct Bitcoin runtime mapping. |
| `sol_get_fees_sysvar` | `!disable_fees_sysvar` | `!disable_fees_sysvar` | SVM cluster or account state. Bitcoin locktime and sequence predicates use transaction data. No direct Bitcoin runtime mapping. |
| `sol_get_rent_sysvar` | Direct | Direct | SVM cluster or account state. Bitcoin locktime and sequence predicates use transaction data. No direct Bitcoin runtime mapping. |
| `sol_get_last_restart_slot` | `last_restart_slot_syscall_enabled` | `last_restart_slot_syscall_enabled` | SVM cluster or account state. Bitcoin locktime and sequence predicates use transaction data. No direct Bitcoin runtime mapping. |
| `sol_get_epoch_rewards_sysvar` | Direct | Direct | SVM cluster or account state. Bitcoin locktime and sequence predicates use transaction data. No direct Bitcoin runtime mapping. |
| `sol_memcpy_` | Direct | Direct | SVM memory/address-space operation. Fixed typed data and equality express bounded relations without the allocator or memory ABI. |
| `sol_memmove_` | Direct | Direct | SVM memory/address-space operation. Fixed typed data and equality express bounded relations without the allocator or memory ABI. |
| `sol_memset_` | Direct | Direct | SVM memory/address-space operation. Fixed typed data and equality express bounded relations without the allocator or memory ABI. |
| `sol_memcmp_` | Direct | Direct | SVM memory/address-space operation. Fixed typed data and equality express bounded relations without the allocator or memory ABI. |
| `sol_get_processed_sibling_instruction` | Direct | Direct | SVM execution-stack or inter-instruction state. Bitcoin input/output introspection has a different source and lifecycle. |
| `sol_get_stack_height` | Direct | Direct | SVM execution-stack or inter-instruction state. Bitcoin input/output introspection has a different source and lifecycle. |
| `sol_set_return_data` | Direct | Direct | SVM execution-stack or inter-instruction state. Bitcoin input/output introspection has a different source and lifecycle. |
| `sol_get_return_data` | Direct | Direct | SVM execution-stack or inter-instruction state. Bitcoin input/output introspection has a different source and lifecycle. |
| `sol_invoke_signed_c` | Direct | Direct | SVM signed cross-program invocation and account mutation. Simplicity delegation and Bitcoin state outputs use separate authorization and state semantics. |
| `sol_invoke_signed_rust` | Direct | Direct | SVM signed cross-program invocation and account mutation. Simplicity delegation and Bitcoin state outputs use separate authorization and state semantics. |
| `sol_invoke_signed_v2` | `invoke_signed_v2` | Absent | SVM signed cross-program invocation and account mutation. Simplicity delegation and Bitcoin state outputs use separate authorization and state semantics. |
| `sol_alloc_free_` | `!reject_deployment_of_broken_elfs` | `!disable_deploy_of_alloc_free_syscall` | SVM memory/address-space operation. Fixed typed data and equality express bounded relations without the allocator or memory ABI. |
| `sol_alt_bn128_group_op` | `enable_alt_bn128_syscall` | `enable_alt_bn128_syscall` | BN254 G1/G2 group and pairing work. Fp/Fp2 kernels and the Groth16 estimate cover arithmetic components only. Newer G2 and little-endian variants have operation gates. |
| `sol_big_mod_exp` | `enable_big_mod_exp_syscall` | `enable_big_mod_exp_syscall` | Wide division and multiply kernels supply components. The variable-width modular-exponentiation and SBF error ABI are outside the measured relations. |
| `sol_poseidon` | `enable_poseidon_syscall` | `enable_poseidon_syscall` | The syscall hashes with the Solana Poseidon parameter API. crypto-poseidon2-koalabear16 uses a different field and permutation. There is no exact match. |
| `sol_remaining_compute_units` | `remaining_compute_units_syscall_enabled` | `remaining_compute_units_syscall_enabled` | SVM budget introspection. Bitcoin Simplicity has a caller-supplied budget and static cost bound. No equivalent spend-time meter predicate. |
| `sol_alt_bn128_compression` | `enable_alt_bn128_compression_syscall` | `enable_alt_bn128_compression_syscall` | BN254 G1/G2 compressed encoding and reconstruction. Field multiplication alone does not cover point encoding and validation. The newer source separately gates little-endian variants. |
| `sol_get_sysvar` | `get_sysvar_syscall_enabled` | `get_sysvar_syscall_enabled` | SVM cluster or account state. Bitcoin locktime and sequence predicates use transaction data. No direct Bitcoin runtime mapping. |
| `sol_get_epoch_stake` | `enable_get_epoch_stake_syscall` | `enable_get_epoch_stake_syscall` | SVM cluster or account state. Bitcoin locktime and sequence predicates use transaction data. No direct Bitcoin runtime mapping. |
| `sol_log_data` | Direct | Direct | SVM logging and observability. No Bitcoin spending predicate. |

The newer curve-dispatch code gates secp256r1 operation IDs with secp256r1_syscall_enabled independently of the top-level symbols. BN254 uses separate gates for its top-level group and compression entries and for newer G2 or little-endian variants inside those entries. The Solana Ed25519, secp256k1 and secp256r1 signature programs are native transaction precompiles rather than entries in either sBPF registration table. Their instruction offsets, batch rules and signature constraints are separate from both the SBF curve interfaces and the corpus's typed signature equations. [Pinned Agave dispatch](https://github.com/anza-xyz/agave/blob/84ca856dc20c509a6140c7b4310fa60c209feaaf/syscalls/src/lib.rs#L956-L1973), [BN254 handlers](https://github.com/anza-xyz/agave/blob/84ca856dc20c509a6140c7b4310fa60c209feaaf/syscalls/src/lib.rs#L2200-L2602), [Solana signature precompiles](https://solana.com/docs/core/programs/precompiles).

## Evidence and verification

The manifest records immutable source URLs, revisions, byte counts, SHA-256 hashes, license evidence, and both table hashes. The registration TSVs preserve the source row numbers for each interface and the exact local registration condition for Solana. To reproduce, fetch each manifest source by its immutable URL and verify its SHA-256. Compare the Geth Osaka map entries with the 18 address/implementation rows. In each Agave function listed above, enumerate every ordinary registration call and every feature-gated registration macro. Compare symbols, conditions and line numbers with the TSV. The sets have 18, 44 and 40 unique names or addresses. The 40 Foundation reference names agree exactly with the v3.1.8 source set. No upstream code was executed. [Manifest](data/cross-ecosystem-interface-provenance.json), [Ethereum registration data](data/ethereum-mainnet-precompile-registration.tsv), [Agave registration data](data/agave-syscall-registration.tsv).
