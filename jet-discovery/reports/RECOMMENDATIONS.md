# Recommendations: missing Bitcoin Simplicity jets

Evidence-based recommendations from 49 tested corpus programs (reports/corpus-results.md, corpus/README.md).
Every program passes all its vectors: 605 vectors, 343 of them in programs whose vectors come from upstream
test-vector files (BIPs, RFCs). Method: reports/METHOD.md.

**Cost labels.**
- Plain numbers are measured static cost bounds in WU.
- **ESTIMATE** marks any cost involving a hypothetical jet. Each one is scaled from an existing benchmark, with the
  method given in candidates/<name>/README.md.

**Budget caveat.** The Bitcoin budget rule is not defined in this repository (reports/mismatches.md #5). The
rankings below do not depend on it. Feasibility claims are marked as using the ASSUMPTION budget = witness bytes + 50.

**Correction (2026-11-03).** The per-jet ESTIMATE costs printed in the candidate READMEs of the previous version
were half the values the what-if overlay actually used: they were computed without the library's 0.5 batch
adjustment on `CheckSigVerify` (`Simplicity.Bitcoin.Benchmarks.benchmark`). All what-if program costs were
correct; the READMEs and the monolithic `shrincs_verify` estimate are now fixed.

## Summary

1. **Most covenant proposals are already cheap in Simplicity, if you accept Simplicity-native hashes.**
   CTV-equivalent (37.7 WU), APO-style rebindable signatures (88.5), CSFS (51.8 for 32-byte messages),
   INTERNALKEY (54.2), PAIRCOMMIT (136.8), CCV (183.7), TLUV (193.3), TWEAKADD (196.4), MERKLEBRANCHVERIFY
   (145.7), tail calls (54.2), a P2MR covenant (50.5) and a vault (130.4) all cost no more than a few signature
   checks. Cross-input semantics (CCV aggregation, batched vault recovery) cost 170-344 WU with a per-input rescan.
2. **Hash compatibility with the BIPs is what is expensive, except where the BIP hashes what Simplicity exposes.**
   - The exact BIP 119 (3,737 WU), BIP 446 (1,937 WU) and BIP 448 (1,987 WU) programs spend over 95% of their
     bound re-serializing outputs from witness bytes. One jet family exposing BIP 341's precomputed hashes would
     cut these by 34-69x (ESTIMATE).
   - Exact BIP 346 TXHASH costs 1,996 WU and passes all 150 upstream vectors with existing jets: its per-field
     hashes are built from data Simplicity's primitives already expose (script hashes, values, sequences).
3. **Post-quantum signatures are the strongest Bitcoin-specific case.**
   - SHRINCS stateful verification costs 8,039 WU; the stateless (SLH-DSA) path costs 58,345 WU.
   - A generic SHA-256 tweaked-chain jet brings them to 1,199 and 20,938 WU (6.7x and 2.8x, ESTIMATE). With it,
     both fit the ASSUMPTION budget (signatures of 619 and 5,520 bytes); without it, neither does.
   - The intrinsic SHA-256 work is ~390 WU stateful and ~2,136 WU stateless (ESTIMATE), so the stateless path
     still spends ~19,000 WU in tweakable-hash plumbing after the chain jet.
4. **Plumbing, not arithmetic, dominates.** Across the corpus, the static bound charges for moving data through
   compositions:
   - SHA-256 contexts: ~830 bits, about 1 WU per step.
   - Witness buffers: about 4 WU per 511-byte slot per step.
   - Constants outside unit input type: tens of WU.

   Jets that fuse a whole kernel remove this tax, which is why kernel jets save 5-750x even where the
   arithmetic jets already exist.
5. **Non-native curves need curve-level jets; field jets are not enough.** Now measured, not proxied:
   - ECDSA-P256 verification (RFC 6979 vectors): 8,860,684 WU, 221% of `BUDGET_MAX`. With a P-256 field-multiply
     jet: 702,330 WU (17.6%, ESTIMATE). A curve-level `p256_ecdsa_verify`: ~99 WU (ESTIMATE).
   - Ed25519 verification (RFC 8032 vectors): 2,925,313 WU (73%). With field-multiply and SHA-512 jets:
     557,350 WU (13.9%, ESTIMATE).
   - With field jets the remaining cost is field additions and moving Jacobian points through the
     scalar-multiplication loop.
6. **Cross-chain hashes and STARKs are expressible but heavy; each is a well-defined kernel jet.**
   - RIPEMD-160: 2,470 WU; a HASH160 HTLC: 2,546 WU (28x cheaper with `ripemd160_compress`, ESTIMATE).
   - SHA-512: 5,454; Keccak-256: 5,776; BLAKE2b: 4,642; BLAKE2s: 3,257 WU.
   - A complete circle-FRI verifier (toy parameters: 2^8 domain, 6 folds, 3 queries, real proofs): 9,423 WU;
     2,742 WU with M31/QM31 jets (ESTIMATE). Extrapolated to 30 queries and 20 layers: ~350,000 WU today and
     ~114,000 WU with the jets (ESTIMATE, FRI only).
7. **The eprint constructions and Ethereum/Solana contract patterns need nothing new.**
   - Adaptor signatures (112 WU), MuSig2 KeyAgg of three keys with the BIP 327 vectors (591), a 4-key ring
     signature (500) and a Cashu-style DLEQ proof (298) are all dominated by existing secp256k1 jets.
   - Linear vesting (78), a Dutch auction (46), a 3-of-5 Safe with a spending allowance (287) and oracle-priced
     loan liquidation (139) use only existing jets; the only match is `multiply_128` in the liquidation (1.1x).
   - This agrees with gmax's earlier finding that popular smart contracts are technically boring.

## Ranked candidates

**Score:** corpus WU saved × generality, ÷ verification burden.
- Generality: 3 = primitive used by many schemes, 2 = one ecosystem, 1 = one scheme.
- Burden: 1 = low, 2 = medium, 3 = high, judged against the jets proven on `feat/jet-equivalence`.

WU saved is summed over corpus programs. A program with several matched candidates is attributed by candidate
(reports/whatif.md). The score depends on which programs are in the corpus: SHRINCS's stateless path alone
contributes 175 chain matches. The non-native curve candidates are listed apart, because their savings (millions of
WU) leave the programs infeasible and would swamp the score.

| rank | tier | candidate | corpus WU saved | generality | burden | score | evidence |
| ---: | --- | --- | ---: | :---: | :---: | ---: | --- |
| 1 | strong | [`sha256_wots_chain_16`](../candidates/sha256_wots_chain_16/README.md) | 44,247 | 3 | 2 | 66,371 | SHRINCS stateful 8,039 → 1,199; stateless 58,345 → 20,938 |
| 2 | maybe | [`m31_mul`](../candidates/m31_mul/README.md) + [`qm31_mul`](../candidates/qm31_mul/README.md) | 7,825 | 1.5 | 1 | 11,738 | FRI verifier 9,423 → 2,742; FRI fold 347 → 66.7; M31 inverse 698 → 83.7 |
| 3 | strong | [`bip341_hashes`](../candidates/bip341_hashes/README.md) (sha_outputs, sha_sequences, sha_annex, sha_prevouts, sha_amounts, sha_scriptpubkeys; BIP 119 scriptSig hash) | 7,442 | 3 | 2 | 11,163 | CTV-exact 3,737 → 54.5; TEMPLATEHASH 1,937 → 57.3; LN-Symmetry 1,987 → ~107 |
| 4 | maybe | [`ripemd160_compress`](../candidates/ripemd160_compress/README.md) | 4,911 | 3 | 2 | 7,366 | RIPEMD-160 2,470 → 14.1; HASH160 HTLC 2,546 → 91.1 |
| 5 | maybe | [`sha512_compress`](../candidates/sha512_compress/README.md) | 5,436 | 2 | 2 | 5,436 | SHA-512 5,454 → 17.8 (also inside ed25519) |
| 6 | maybe | [`blake2b_compress`](../candidates/blake2b_compress/README.md) | 4,630 | 2 | 2 | 4,630 | 4,642 → 11.4 |
| 7 | maybe | [`keccak_f1600`](../candidates/keccak_f1600/README.md) | 5,751 | 2 | 3 | 3,834 | 5,776 → 24.3 |
| 8 | maybe | [`multiply_256`](../candidates/multiply_256/README.md) + [`div_mod_512`](../candidates/div_mod_512/README.md) | 3,793 | 2 | 2 | 3,793 | BIP 441 modular multiply 3,808 → 15.3 |
| 9 | maybe | [`blake2s_compress`](../candidates/blake2s_compress/README.md) | 3,252 | 2 | 2 | 3,252 | 3,257 → 4.3 |
| 10 | maybe | [`div_mod_256`](../candidates/div_mod_256/README.md) + [`multiply_128`](../candidates/multiply_128/README.md) | 1,401 | 2 | 2 | 1,401 | Uniswap math 1,410 → 25.3; liquidation 139 → 123 |
| 11 | strong | [`pubkey_unpack_neg`](../candidates/pubkey_unpack_neg/README.md) + [`signature_unpack`](../candidates/signature_unpack/README.md) | 320 | 3 | 1 | 961 | variable-length CSFS 408 → 88 |
| 12 | maybe | [`shrincs_verify`](../candidates/shrincs_verify/README.md) (monolithic) | ~19,600 beyond #1 | 1 | 3 | ~6,500 | ~390 WU stateful / ~2,136 WU stateless (ESTIMATE) |
| 13 | rejected | [`sha256_pair`](../candidates/sha256_pair/README.md) | 66 + a share of the FRI verifier | 3 | 1 | ~200 | Merkle path 241 → 175 (1.4x); existing ctx jets suffice |

**Non-native curves** (measured programs, ESTIMATE jet costs):

| candidate | measured program | with field-level jets | with a curve-level jet | verdict |
| --- | --- | ---: | ---: | --- |
| [`p256_ecdsa_verify`](../candidates/p256_ecdsa_verify/README.md) vs [`p256_fe_multiply`](../candidates/p256_fe_multiply/README.md) | `xchain-p256-ecdsa` 8,860,684 WU (221% of `BUDGET_MAX`) | 702,330 (17.6%) | ~99 | curve-level jet, or nothing |
| `ed25519_verify` (not registered) vs [`ed25519_fe_multiply`](../candidates/ed25519_fe_multiply/README.md) + [`sha512_compress`](../candidates/sha512_compress/README.md) | `xchain-ed25519` 2,925,313 WU (73%) | 557,350 (13.9%) | ~100 (ESTIMATE, by analogy with `bip_0340_verify`) | curve-level jet, or nothing |

### Why `pubkey_unpack_neg` + `signature_unpack` is "strong" despite a low score

The measured saving is small because the corpus has only one program that checks signatures outside the
`bip_0340_verify` jet in a way that needs them. Every custom construction that starts from serialized BIP 340
keys and signatures pays the same 320 WU:
- variable-length CSFS,
- adaptor signatures and oracle attestations over serialized pre-signatures,
- MuSig2 and FROST partial checks.

The corpus's adaptor, ring and DLEQ programs avoid the cost by taking points in decompressed form as witness
operands, which a script interoperating with serialized keys cannot do.

The jets are tiny range checks, a low burden like `fe_normalize`.

An alternative is a single `bip_0340_verify` variant taking a message buffer. It serves CSFS directly, but not the
other constructions.

### Strong (recommend implementing and proving)

1. **`sha256_wots_chain_16`**, plus a single tweakable-hash jet for H, T and FORS leaves.
   - Covers SHRINCS (draft BIP; both paths now measured), SLH-DSA-SHA2 (FIPS 205), XMSS/LMS-style chains and
     BitVM Winternitz commitments.
   - It composes the proven SHA-256 compression with a bounded loop.
   - With it, both SHRINCS paths fit the ASSUMPTION budget. The stateless path's remaining 20,938 WU is mostly
     tweakable-hash plumbing (FORS and hypertree nodes); a `sha256_thash` jet over (seed, address, input) is the
     next step and should be measured before a monolithic `shrincs_verify`.
2. **`bip341_hashes`**
   - Bitcoin Core already computes these hashes (`PrecomputedTransactionData`). Exposing them makes every
     BIP 341-compatible covenant and signature-hash proposal cost about as much as Simplicity's native ones.
   - The alternatives are a raw-bytes script primitive (breaks Simplicity's bounded-type design) or witness
     re-serialization (measured at 34-69x more).
   - Burden: low to medium. These are transaction-hash jets like `outputs_hash`, reusing the proven SHA-256
     streaming lemmas. The new work is a BIP 341 serialization specification over raw scripts in the txEnv.
3. **`pubkey_unpack_neg` / `signature_unpack`**: see above.

### Maybe (worth it if there is demand)

- **`ripemd160_compress`: the Bitcoin-native hash gap.** HASH160 is Script's key hash (P2PKH, P2WPKH) and the BOLT 3
  HTLC payment hash. A Script-compatible HTLC costs 2,546 WU today and ~91 WU with the jet (ESTIMATE). Simplicity's
  own HTLCs can use SHA-256 payment hashes (`app-htlc`: 62 WU), so the demand is interoperability with existing
  Script outputs and Lightning's HASH160 scripts. A `hash160_32` jet would cover both uses in one call.
- **Hash compression jets: SHA-512 (ed25519, BIP 32 HMAC-SHA512), BLAKE2b (EIP-152, Zcash), BLAKE2s/BLAKE3,
  Keccak-f[1600] (Ethereum).**
  - Each turns a 3,000-6,000 WU program into a few WU.
  - Their value is interoperability: bridges, light clients, proof verification.
  - BLAKE2s/BLAKE3 also matter for STARKs. Keccak's burden is the highest of the four (a new permutation).
- **M31/QM31 field jets for circle-STARK verification.**
  - Measured: a complete circle-FRI verifier (Merkle openings, folds, Fiat-Shamir) on real proofs with toy
    parameters costs 9,423 WU, ~520 WU per query-layer; with the jets 2,742 WU (ESTIMATE).
  - Extrapolated to 30 queries and 20 FRI layers (600 query-layers, ~5,700 Merkle levels): ~350,000 WU today
    (8.7% of `BUDGET_MAX`) and ~114,000 WU with the jets (ESTIMATE). The FRI witness would be ~200 KB, so under the
    ASSUMPTION budget the FRI part fits with the jets and not without them.
  - Not counted: trace and composition openings and the DEEP quotient (more Merkle paths and a few hundred
    extension-field operations per query).
- **`multiply_256` + `div_mod_512`** (BIP 441 big numbers: 249x), and **`div_mod_256` + `multiply_128`**
  (fixed-point and AMM math). A fused `mod_mul_256` is what the corpus uses. Also consider an unnormalized
  `div_mod_128_64` (reports/mismatches.md #3).
- **`p256_ecdsa_verify`** (passkeys/WebAuthn, HSMs, RIP-7212) and an **`ed25519_verify`** (Solana, Cardano, SSH):
  - Now measured: field-level jets leave 557,000-702,000 WU (14-18% of `BUDGET_MAX`), which no plausible
    witness-based budget covers. A curve-level jet is required, or nothing.
  - High burden: new curves outside libsecp256k1.
- **`shrincs_verify`:** only if SHRINCS is standardised and the chain and tweakable-hash jets prove insufficient.

### Rejected

- **`sha256_pair`:** 1.4x on Merkle paths. The existing SHA-256 context jets are adequate.
- **Opcode-shaped jets for CTV, CSFS, APO, INTERNALKEY, PAIRCOMMIT, CCV, VAULT, TLUV, TWEAKADD,
  MERKLEBRANCHVERIFY, TXHASH.** Each is already expressible at 38-2,000 WU with existing jets. Hash-compatible
  variants of CTV and TEMPLATEHASH are better served by `bip341_hashes` than by one jet per opcode.
- **OP_CAT-like byte concatenation.** The SHA-256 context jets already stream arbitrary byte layouts into hashes,
  which covers CAT's main uses (Merkle paths, PAIRCOMMIT).
- **64-bit arithmetic and comparisons.** The jets exist (`app-dlc-cfd`: 105 WU; the Ethereum/Solana patterns: 46-287 WU).
- **A cross-input aggregation jet** (sum of values of same-script inputs). Measured at 344 WU for CCV aggregation
  and 170 WU for batched vault recovery over 16 inputs: not worth a jet.
- **Multi-scalar multiplication for MuSig2/ring signatures.** KeyAgg of three keys costs 591 WU with `scale`; the
  ring signature 500 WU with `linear_combination_1`.

## Per-BIP verdicts

| proposal | verdict | program (cost) |
| --- | --- | --- |
| BIP 116 MERKLEBRANCHVERIFY (with BIP 98 fast Merkle trees) | expressible as is (fast-SHA256 via the SHA-256 block jet with BIP 98's IV) | `bip116-merklebranchverify` (145.7) |
| BIP 117 tail call | expressible as is, as delegation (`disconnect`) | `bip117-tail-call` (54.2) |
| BIP 118 ANYPREVOUT | expressible as is, as a Simplicity sighash mode; a BIP 118-compatible digest needs `bip341_hashes` | `bip118-apo` (88.5) |
| BIP 119 CTV | expressible as is (native hashes); hash-compatible needs `bip341_hashes` | `bip119-ctv-native` (37.7), `bip119-ctv-exact` (3,737; 100 upstream txs) |
| BIP 345 OP_VAULT | expressible as is (data-tweak + native template); batched recovery by per-input rescan | `app-vault` (130.4), `app-vault-batch-recover` (170.0) |
| BIP 346 OP_TXHASH | expressible as is, hash-compatible: all 150 upstream vectors | `bip346-txhash` (1,996) |
| BIP 347 OP_CAT | no jet needed: its uses are expressible | `app-merkle-key` (240.7), `bip442-paircommit` (136.8) |
| BIP 348 OP_CHECKSIGFROMSTACK | expressible as is; variable-length messages benefit from unpack jets | `bip348-csfs-32` (51.8), `bip348-csfs` (408.3 → 87.9) |
| BIP 349 OP_INTERNALKEY | expressible as is (existing `internal_key` jet) | `bip349-internalkey` (54.2) |
| BIP 360 P2MR | expressible as is (a covenant producing a P2MR output) | `bip360-p2mr-output` (50.5) |
| BIP 440 varops budget | a budget rule, not an opcode: no program; relevant to the open budget question | – |
| BIP 441 restored big-number opcodes | expressible but heavy; `multiply_256` + `div_mod_512` | `bip441-bignum-modmul` (3,808 → 15.3) |
| BIP 442 OP_PAIRCOMMIT | expressible as is | `bip442-paircommit` (136.8) |
| BIP 443 OP_CHECKCONTRACTVERIFY | expressible as is; the default mode's cross-input amount accounting by per-input rescan | `bip443-ccv-output` (183.7), `bip443-ccv-aggregate` (344.0) |
| BIP 446 OP_TEMPLATEHASH | hash-compatible needs `bip341_hashes` | `bip446-templatehash-exact` (1,937; 19 upstream cases) |
| BIP 448 (TEMPLATEHASH + CSFS + INTERNALKEY, LN-Symmetry) | needs `bip341_hashes` for hash compatibility; the native version is ~90 WU | `bip448-lnsymmetry-update` (1,987) |
| BIP 449 OP_TWEAKADD | expressible as is (upstream vectors) | `bip449-tweakadd` (196.4) |
| TLUV (no BIP) | expressible as is (taptweak jets) | `tluv-remove-leaf` (193.3) |
| LNHANCE (CTV + CSFS + INTERNALKEY + PAIRCOMMIT) | every component expressible; exact CTV needs `bip341_hashes` | components above |
| 64-bit arithmetic | expressible as is (jets exist; division needs a normalized divisor) | `app-dlc-cfd` (105.3) |
| SHRINCS (post-quantum) | expressible but expensive; needs `sha256_wots_chain_16` (then a tweakable-hash jet) | `pq-shrincs-stateful` (8,039 → 1,199), `pq-shrincs-stateless` (58,345 → 20,938) |
| Circle STARK verification | expressible but expensive; needs M31/QM31 jets | `stark-fri-verifier` (9,423 → 2,742); ~350k WU per full-size FRI (ESTIMATE) |

## Cross-ecosystem inventory (Phase 1 item 5)

**Ethereum precompiles.**

| precompile | status in this study |
| --- | --- |
| ecrecover (secp256k1 ECDSA) | existing secp256k1 jets suffice in principle; not implemented |
| sha256 | jet exists |
| ripemd160 | measured: 2,470 WU; `ripemd160_compress` |
| identity | n/a |
| modexp | `multiply_256` / `div_mod_512` family (BIP 441 program) |
| bn254 add/mul/pairing, BLS12-381 (EIP-2537), KZG point evaluation | excluded: no Bitcoin deployment path found; very high verification burden |
| blake2f (EIP-152) | `blake2b_compress` |
| P256VERIFY (RIP-7212) | measured: 8.86M WU; `p256_ecdsa_verify` |

**Solana syscalls.**

| syscall | status in this study |
| --- | --- |
| sha256 | jet exists |
| keccak256 | `keccak_f1600` |
| blake3 | `blake2s_compress` (same G function) |
| secp256k1_recover | as ecrecover |
| curve25519 / ed25519 | measured: 2.93M WU; a curve-level jet |
| alt_bn128 | excluded, as above |
| poseidon | excluded |
| big_mod_exp | modexp |

**Contract patterns** (all measured, all cheap; `src/JetDiscovery/Corpus/EthSol.hs`):

| pattern | origin | program (cost) |
| --- | --- | --- |
| linear vesting | OpenZeppelin VestingWallet, Solana token-vesting | `ethsol-linear-vesting` (77.6) |
| descending-price auction | Seaport, Metaplex, Paradigm GDA (linear) | `ethsol-dutch-auction` (45.7) |
| threshold wallet with a delegate allowance | Safe + AllowanceModule | `ethsol-safe-allowance` (287.4) |
| oracle-priced liquidation | Aave, Compound, Solend | `ethsol-lending-liquidation` (138.7 → 122.9) |
| constant-product swap math | Uniswap v2 | `xchain-uniswap-v2-amount-out` (1,410 → 25.3) |

## Eprint scan (filtered)

Included and measured, each with a credible Bitcoin deployment path:
- **SHRINCS** (Kudinov & Nick, ePrint 2025/2203). Post-quantum signatures for Bitcoin, already deployed via
  Simplicity on Liquid. Measured: `pq-shrincs-stateful`, `pq-shrincs-stateless`.
- **Circle STARKs** (Haböck, Levit & Papini, ePrint 2024/278). StarkWare's Bitcoin verifier work makes this the
  STARK most likely to be verified on Bitcoin. Measured: `stark-fri-verifier` and the `stark-*` kernels.
- **Adaptor signatures** (PTLCs, DLCs, atomic swaps): `eprint-adaptor-sig` (112.4).
- **MuSig2 key aggregation** (BIP 327, ePrint 2020/1261), against BIP 327's own vectors: `eprint-musig2-keyagg` (590.9).
- **Ring signatures** (Abe-Ohkubo-Suzuki; proof of reserves without revealing the key): `eprint-ring-sig` (499.6).
- **Chaum-Pedersen DLEQ proofs** (Cashu ecash, NUT-12): `eprint-dleq-cashu` (298.0).

None of the last four needs a new jet: the existing `scale`, `linear_combination_1`, `linear_verify_1` and
`decompress` jets do the work.

Considered, and needing no new jets:
- **FROST**: aggregate keys verify as plain BIP 340; partial-signature checks are `linear_verify_1` like the
  adaptor program.

Excluded:
- **Lattice signatures (ML-DSA, FIPS 204).** A possible post-quantum alternative, but its NTT arithmetic would need
  a new jet family, and Bitcoin's post-quantum work has converged on hash-based schemes.
- **Pairing-based schemes (BLS aggregation, Groth16 verification).** No Bitcoin soft-fork proposal; high burden.
- **Bulletproofs.** No confidential amounts on Bitcoin.

## Non-jet findings (for the library and the soft-fork design)

1. **Constant cost depends on context** (mismatches.md #1). `scribe` constants at non-unit input types cost tens
   of WU instead of ~0.3. `CheckSig.sigHash` loses about 150 WU this way when used outside its jet. Compilers
   should emit `unit >>> scribe c`.
2. **Context-threading tax.** Each composition charges the bit size of its intermediate value, so programs that
   thread a SHA-256 context pay ~1 WU per step around 0.7-1.2 WU context jets. Hash APIs that take and return
   smaller state (a midstate plus a counter) would lower this tax without new kernels.
3. **Static worst-case pricing.** Loop bounds and maximum buffer sizes are always paid. Exact CTV costs 3,737 WU
   even for a one-output transaction. This argues for both the `bip341_hashes` family and a budget rule that
   counts the witness.
4. **The budget rule is undecided** (mismatches.md #5). Under the ASSUMPTION budget, the exact covenant programs,
   SHRINCS, the FRI verifier and the cross-chain hash kernels need witness padding, and the native covenant
   programs, eprint constructions and contract patterns do not.
5. **`Simplicity.Bitcoin.StaticAnalysis.Cost` is not re-exported** (mismatches.md #2). It would be a one-line
   cabal change. Not applied here: off-limits.
6. **Witness hints make non-native arithmetic cheaper.** The P-256 and ed25519 programs take an inverse and
   decompression x-coordinates as witness and only check them (s⁻¹ mod n for P-256; x of R and A for ed25519). Library or compiler support
   for this check-don't-compute pattern matters as much as jets for non-native code.

## Limitations

- **Corpus bias.**
  - One author and one library. Programs were written to force the expensive work: exact serializations,
    variable-length messages, post-quantum verification.
  - SimplicityHL-compiled programs may differ in plumbing costs.
- **Estimates.**
  - Every candidate cost is scaled from an existing benchmark, not measured.
  - The full-size STARK costs are extrapolated from the measured toy verifier; trace/composition openings and the
    DEEP quotient are not included.
  - All of them need C implementations and benchmarks.
- **Not implemented.**
  - ecrecover-style ECDSA over secp256k1, FROST partial-signature checks.
  - Elements is out of scope.
- **Simplifications stated per program** (corpus/README.md): for example TXHASH takes the selector decoded
  off-chain and the tapscript-context fields as witness operands; the Ethereum/Solana patterns use the lock time
  as their clock.
- **Derived vectors.**
  - 262 of the 605 vectors are in programs with derived vectors (Haskell references).
  - For SHRINCS, the upstream vectors are published only as fingerprints. A misreading shared by the
    transcription and the program would go unnoticed.
- **Static bounds versus CPU time.** All costs are the static bound the budget is checked against, not measured
  CPU time.
- **Verification burden.** The burden column is a judgement by analogy, not a measured proof effort.

## Reproduction

All in `jet-discovery/`. Expected results: all 49 programs pass, 16 tests pass. A full `run` takes tens of
minutes, mostly executing the P-256 and ed25519 vectors.

The existing in-tree suites also passed unchanged at commit 34921e86 (no files outside `jet-discovery/` have
changed since):
- C: `make check` on an archive of `C/`: 98 successes, 0 failures.
- Haskell: `Simplicity:test:testsuite`, through a scratch cabal project with tests enabled and
  `--quickcheck-tests=20`: all 3,252 tests passed.

```bash
nix-shell --run 'cabal build all'
```

```bash
nix-shell --run 'cabal run -v0 exe:jet-discovery -- run'
```

```bash
nix-shell --run 'cabal test'
```
