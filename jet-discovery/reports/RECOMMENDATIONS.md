# Recommendations: missing Bitcoin Simplicity jets

Evidence-based recommendations from 25 tested corpus programs (reports/corpus-results.md, corpus/README.md).
Every program passes all its vectors: 341 vectors, 155 of them from upstream test-vector files.
Method: reports/METHOD.md.

**Cost labels.**
- Plain numbers are measured static cost bounds in WU.
- **ESTIMATE** marks any cost involving a hypothetical jet. Each one is scaled from an existing benchmark, with the
  method given in candidates/<name>/README.md.

**Budget caveat.** The Bitcoin budget rule is not defined in this repository (reports/mismatches.md #5). The
rankings below do not depend on it. Feasibility claims are marked as using the ASSUMPTION budget = witness bytes + 50.

## Summary

1. **Most covenant proposals are already cheap in Simplicity, if you accept Simplicity-native hashes.**
   CTV-equivalent (37.7 WU), APO-style rebindable signatures (88.5), CSFS (51.8 for 32-byte messages),
   INTERNALKEY (54.2), PAIRCOMMIT (136.8), CCV (183.7) and a vault (130.4) all cost no more than a few signature
   checks.
2. **Hash compatibility with the BIPs is what is expensive.**
   - The exact BIP 119 (3,737 WU), BIP 446 (1,937 WU) and BIP 448 (1,987 WU) programs spend over 95% of their
     bound re-serializing outputs from witness bytes.
   - The reason: Bitcoin Simplicity exposes only hashes of scripts, and every buffer slot is priced at its maximum
     size.
   - One jet family exposing BIP 341's precomputed hashes would cut these by 34-69x (ESTIMATE).
3. **Post-quantum signatures are the strongest Bitcoin-specific case.**
   - SHRINCS stateful verification costs 8,039 WU, 89.7% of it in Winternitz chains, against an intrinsic
     ~195 WU of SHA-256 work.
   - A generic SHA-256 tweaked-chain jet brings it to 1,199 WU (6.7x, ESTIMATE) and serves SLH-DSA (FIPS 205) too.
4. **Plumbing, not arithmetic, dominates.** Across the corpus, the static bound charges for moving data through
   compositions:
   - SHA-256 contexts: ~830 bits, about 1 WU per step.
   - Witness buffers: about 4 WU per 511-byte slot per step.
   - Constants outside unit input type: tens of WU.

   Jets that fuse a whole kernel remove this tax, which is why kernel jets save 5-750x even where the
   arithmetic jets already exist.
5. **Cross-chain and STARK primitives are expressible but heavy.**
   - Keccak-256: 5,776 WU.
   - BLAKE2b compression: 4,642 WU.
   - One QM31 multiply: 246 WU.
   - A circle-STARK verifier: roughly 236,000 WU (ESTIMATE).

   Each is a well-defined, verifiable kernel jet. Whether they are worth a consensus change is a demand
   question, not a technical one.

## Ranked candidates

**Score:** corpus WU saved × generality, ÷ verification burden.
- Generality: 3 = primitive used by many schemes, 2 = one ecosystem, 1 = one scheme.
- Burden: 1 = low, 2 = medium, 3 = high, judged against the jets proven on `feat/jet-equivalence`.

WU saved is summed over corpus programs. A program with several matched candidates is attributed by candidate
(reports/whatif.md).

| rank | tier | candidate | corpus WU saved | generality | burden | score | evidence |
| ---: | --- | --- | ---: | :---: | :---: | ---: | --- |
| 1 | strong | [`bip341_hashes`](../candidates/bip341_hashes/README.md) (sha_outputs, sha_sequences, sha_annex, sha_prevouts, sha_amounts, sha_scriptpubkeys; BIP 119 scriptSig hash) | 7,442 | 3 | 2 | 11,163 | CTV-exact 3,737 → 54.5; TEMPLATEHASH 1,937 → 57.3; LN-Symmetry 1,987 → ~107 |
| 2 | strong | [`sha256_wots_chain_16`](../candidates/sha256_wots_chain_16/README.md) | 6,840 | 3 | 2 | 10,260 | SHRINCS 8,039 → 1,199; top mined sub-DAG (21.3% of the corpus bound) |
| 3 | maybe | [`blake2b_compress`](../candidates/blake2b_compress/README.md) | 4,630 | 2 | 2 | 4,630 | 4,642 → 11.4 |
| 4 | maybe | [`keccak_f1600`](../candidates/keccak_f1600/README.md) | 5,751 | 2 | 3 | 3,834 | 5,776 → 24.3 |
| 5 | maybe | [`blake2s_compress`](../candidates/blake2s_compress/README.md) | 3,252 | 2 | 2 | 3,252 | 3,257 → 4.3 |
| 6 | maybe | [`m31_mul`](../candidates/m31_mul/README.md) + [`qm31_mul`](../candidates/qm31_mul/README.md) | 1,144 | 1.5 | 1 | 1,716 | FRI fold 347 → 66.7; QM31 mul 246 → 5.8; M31 inverse 698 → 83.7 |
| 7 | maybe | [`div_mod_256`](../candidates/div_mod_256/README.md) + [`multiply_128`](../candidates/multiply_128/README.md) | 1,385 | 2 | 2 | 1,385 | Uniswap math 1,410 → 25.3 |
| 8 | strong | [`pubkey_unpack_neg`](../candidates/pubkey_unpack_neg/README.md) + [`signature_unpack`](../candidates/signature_unpack/README.md) | 320 | 3 | 1 | 961 | variable-length CSFS 408 → 88 |
| 9 | maybe | [`p256_ecdsa_verify`](../candidates/p256_ecdsa_verify/README.md) | (proxy) | 3 | 3 | – | without curve-level jets, ECDSA-class verification costs ~2.4M WU (60% of BUDGET_MAX) |
| 10 | maybe | [`shrincs_verify`](../candidates/shrincs_verify/README.md) (monolithic) | ~1,000 beyond #2 | 1 | 3 | ~330 | ~195 WU stateful / ~1,068 WU stateless (ESTIMATE) |
| 11 | rejected | [`sha256_pair`](../candidates/sha256_pair/README.md) | 66 | 3 | 1 | 198 | Merkle path 241 → 175 (1.4x); existing ctx jets suffice |

### Why `pubkey_unpack_neg` + `signature_unpack` is "strong" despite a low score

The measured saving is small because the corpus has only one program that checks signatures outside the
`bip_0340_verify` jet. But every custom signature construction pays the same 320 WU:
- variable-length CSFS,
- adaptor signatures,
- MuSig2 and FROST partial checks,
- oracle attestations over non-32-byte messages.

The jets are tiny range checks, a low burden like `fe_normalize`.

An alternative is a single `bip_0340_verify` variant taking a message buffer. It serves CSFS directly, but not the
other constructions.

### Strong (recommend implementing and proving)

1. **`bip341_hashes`**
   - Bitcoin Core already computes these hashes (`PrecomputedTransactionData`). Exposing them makes every
     BIP 341-compatible covenant and signature-hash proposal cost about as much as Simplicity's native ones.
   - The alternatives are a raw-bytes script primitive (breaks Simplicity's bounded-type design) or witness
     re-serialization (measured at 34-69x more).
   - Burden: low to medium. These are transaction-hash jets like `outputs_hash`, reusing the proven SHA-256
     streaming lemmas. The new work is a BIP 341 serialization specification over raw scripts in the txEnv.
2. **`sha256_wots_chain_16`**, plus a single tweakable-hash jet for H, T and FORS leaves.
   - Covers SHRINCS (draft BIP), SLH-DSA-SHA2 (FIPS 205), XMSS/LMS-style chains and BitVM Winternitz commitments.
   - It composes the proven SHA-256 compression with a bounded loop.
   - Recommended before a monolithic `shrincs_verify`: most of the saving, for a fraction of the proof.
3. **`pubkey_unpack_neg` / `signature_unpack`**: see above.

### Maybe (worth it if there is demand)

- **Hash compression jets: BLAKE2b (EIP-152, Zcash), BLAKE2s/BLAKE3, Keccak-f[1600] (Ethereum).**
  - Each turns a 3,000-6,000 WU program into a few WU.
  - Their value is interoperability: bridges, light clients, proof verification.
  - BLAKE2s/BLAKE3 also matter for STARKs. Keccak's burden is the highest of the three (a new permutation).
- **M31/QM31 field jets for circle-STARK verification.** ESTIMATE for a whole verifier, from the measured kernels:
  - Assumed parameters: Q = 30 queries, L = 20 FRI layers, three Merkle trees of depth 20. That gives 600 folds
    and 2,400 Merkle levels.
  - Today: 600 × 346.9 + 2,400 × 11.6 ≈ 236,000 WU (5.9% of BUDGET_MAX).
  - With `m31_mul` / `qm31_mul` (and `sha256_pair`): 600 × 66.7 + 2,400 × 7.5 ≈ 58,000 WU.
  - The proof's witness would be about 77 KB. Under the ASSUMPTION budget, a STARK verifier would therefore fit
    with these jets but not without them.
  - DEEP/OODS evaluation is not counted: a few hundred extension-field operations.
  - A whole verifier was not written; the parameters are assumptions.
- **`div_mod_256`, `multiply_128`:** big-number arithmetic (the Great Script Restoration's use cases,
  fixed-point/AMM math, non-native field reduction). Also consider an unnormalized `div_mod_128_64`
  (reports/mismatches.md #3).
- **`p256_ecdsa_verify`:** passkeys/WebAuthn and HSMs.
  - The ablation proxy shows field-level jets would not be enough. A curve-level jet is required, or nothing.
  - High burden: a new curve outside libsecp256k1.
- **`shrincs_verify`:** only if SHRINCS is standardised and the chain jet proves insufficient.

### Rejected

- **`sha256_pair`:** 1.4x on Merkle paths. The existing SHA-256 context jets are adequate.
- **Opcode-shaped jets for CTV, CSFS, APO, INTERNALKEY, PAIRCOMMIT, CCV, VAULT.** Each is already expressible at
  38-184 WU with existing jets. Hash-compatible variants are better served by `bip341_hashes` than by one jet per
  opcode.
- **OP_CAT-like byte concatenation.** The SHA-256 context jets already stream arbitrary byte layouts into hashes,
  which covers CAT's main uses (Merkle paths, PAIRCOMMIT).
- **64-bit arithmetic.** The jets exist (`app-dlc-cfd`: 105 WU).

## Per-BIP verdicts

| proposal | verdict | program (cost) |
| --- | --- | --- |
| BIP 119 CTV | expressible as is (native hashes); hash-compatible needs `bip341_hashes` | `bip119-ctv-native` (37.7), `bip119-ctv-exact` (3,737; 100 upstream txs) |
| BIP 118 ANYPREVOUT | expressible as is, as a Simplicity sighash mode; a BIP 118-compatible digest needs `bip341_hashes` | `bip118-apo` (88.5) |
| BIP 345 OP_VAULT | expressible as is (data-tweak + native template); cross-input accounting not modelled | `app-vault` (130.4) |
| BIP 346 OP_TXHASH | not implemented; its fields are BIP 341-style hashes, so it would need `bip341_hashes` (expected like TEMPLATEHASH) | – |
| BIP 347 OP_CAT | no jet needed: its uses are expressible | `app-merkle-key` (240.7), `bip442-paircommit` (136.8) |
| BIP 348 OP_CHECKSIGFROMSTACK | expressible as is; variable-length messages benefit from unpack jets | `bip348-csfs-32` (51.8), `bip348-csfs` (408.3 → 87.9) |
| BIP 349 OP_INTERNALKEY | expressible as is (existing `internal_key` jet) | `bip349-internalkey` (54.2) |
| BIP 442 OP_PAIRCOMMIT | expressible as is | `bip442-paircommit` (136.8) |
| BIP 443 OP_CHECKCONTRACTVERIFY | expressible as is for one input; the default mode's cross-input amount accounting needs each input to rescan all inputs (not modelled) | `bip443-ccv-output` (183.7) |
| BIP 446 OP_TEMPLATEHASH | hash-compatible needs `bip341_hashes` | `bip446-templatehash-exact` (1,937; 19 upstream cases) |
| BIP 448 (TEMPLATEHASH + CSFS + INTERNALKEY, LN-Symmetry) | needs `bip341_hashes` for hash compatibility; the native version is ~90 WU | `bip448-lnsymmetry-update` (1,987) |
| LNHANCE (CTV + CSFS + INTERNALKEY + PAIRCOMMIT) | every component expressible; exact CTV needs `bip341_hashes` | components above |
| 64-bit arithmetic | expressible as is (jets exist; division needs a normalized divisor) | `app-dlc-cfd` (105.3) |
| Great Script Restoration (big numbers) | partly: needs `multiply_128` / `div_mod_256` for comfortable use | `xchain-uniswap-v2-amount-out` (1,410) |
| TLUV | not implemented; expected like CCV (the taptweak jets exist) | – |
| SHRINCS (post-quantum) | expressible but expensive; needs `sha256_wots_chain_16` (or `shrincs_verify`) | `pq-shrincs-stateful` (8,039 → 1,199) |
| Circle STARK verification | expressible but expensive; needs M31/QM31 jets | `stark-*` kernels; ~236k WU ESTIMATE per verifier |

## Cross-ecosystem inventory (Phase 1 item 5)

**Ethereum precompiles.**

| precompile | status in this study |
| --- | --- |
| ecrecover (secp256k1 ECDSA) | existing secp256k1 jets suffice in principle; not implemented |
| sha256 | jet exists |
| ripemd160 | **gap, not measured**: no RIPEMD-160 jet, and Script's HASH160 uses it (BOLT HTLC payment hashes, P2PKH/P2WPKH key hashes) |
| identity | n/a |
| modexp | `div_mod_256` / `multiply_128` family |
| bn254 add/mul/pairing, BLS12-381 (EIP-2537), KZG point evaluation | excluded: no Bitcoin deployment path found; very high verification burden |
| blake2f (EIP-152) | `blake2b_compress` |
| P256VERIFY (RIP-7212) | `p256_ecdsa_verify` |

**Solana syscalls.**

| syscall | status in this study |
| --- | --- |
| sha256 | jet exists |
| keccak256 | `keccak_f1600` |
| blake3 | `blake2s_compress` (same G function) |
| secp256k1_recover | as ecrecover |
| curve25519 / ristretto (ed25519) | not measured; would be a curve-level jet like P-256 (same ablation argument) |
| alt_bn128 | excluded, as above |
| poseidon | excluded |
| big_mod_exp | modexp |

**Recommended follow-up:** measure RIPEMD-160. It is the one gap with direct Bitcoin-native demand: Script
compatibility of HTLCs and key hashes.

## Eprint scan (filtered)

Included, each with a credible Bitcoin deployment path:
- **SHRINCS** (Kudinov & Nick, ePrint 2025/2203). Post-quantum signatures for Bitcoin, already deployed via
  Simplicity on Liquid. Measured: `pq-shrincs-stateful`.
- **Circle STARKs** (Haböck, Levit & Papini, ePrint 2024/278). StarkWare's Bitcoin verifier work makes this the
  STARK most likely to be verified on Bitcoin. Measured: the `stark-*` kernels.

Considered, and needing no new jets:
- **MuSig2** (BIP 327) and **FROST**: aggregate keys verify as plain BIP 340.
- **Adaptor signatures and PTLCs**: existing curve jets (`linear_verify_1`, `gej_*`), plus the unpack jets for
  custom checks.

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
   thread a SHA-256 context pay ~1 WU per step around 0.3-0.5 WU jets. Hash APIs that take and return smaller state
   (a midstate plus a counter) would lower this tax without new kernels.
3. **Static worst-case pricing.** Loop bounds and maximum buffer sizes are always paid. Exact CTV costs 3,737 WU
   even for a one-output transaction. This argues for both the `bip341_hashes` family and a budget rule that
   counts the witness.
4. **The budget rule is undecided** (mismatches.md #5). Under the ASSUMPTION budget, the exact covenant programs,
   SHRINCS and the cross-chain hash kernels need witness padding, and the native covenant programs do not.
5. **`Simplicity.Bitcoin.StaticAnalysis.Cost` is not re-exported** (mismatches.md #2). It would be a one-line
   cabal change. Not applied here: off-limits.

## Limitations

- **Corpus bias.**
  - One author and one library. Programs were written to force the expensive work: exact serializations,
    variable-length messages, post-quantum verification.
  - SimplicityHL-compiled programs may differ in plumbing costs.
- **Estimates.**
  - Every candidate cost is scaled from an existing benchmark, not measured.
  - The STARK verifier and P-256 costs are extrapolated from kernels and proxies.
  - All of them need C implementations and benchmarks.
- **Not measured or not implemented.**
  - BIP 346 TXHASH, TLUV, the SHRINCS stateless (SLH-DSA) path, a whole STARK verifier, ECDSA-P256, ed25519,
    RIPEMD-160.
  - CCV's and VAULT's cross-input amount semantics.
- **Derived vectors.**
  - 186 of the 341 vectors are derived from Haskell references.
  - For SHRINCS, the upstream vectors are published only as fingerprints. A misreading shared by the
    transcription and the program would go unnoticed.
- **Static bounds versus CPU time.** All costs are the static bound the budget is checked against, not measured
  CPU time.
- **Verification burden.** The burden column is a judgement by analogy, not a measured proof effort.

## Reproduction

All in `jet-discovery/`. Expected results: all 25 programs pass, 8 tests pass. The in-tree C suite was also run
on an archive of this commit (`make check` in C/): 98 successes, 0 failures.

```bash
nix-shell --run 'cabal build all'
```

```bash
nix-shell --run 'cabal run -v0 exe:jet-discovery -- run'
```

```bash
nix-shell --run 'cabal test'
```
