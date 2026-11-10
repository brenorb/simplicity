# Follow-up: the open items after the frozen report

The frozen evidence run (RECOMMENDATIONS.md, fingerprint
`5e8dc436…29f0`) listed work it left open. This report covers what was done
afterwards, what changed, and what is still open. Everything here is
supplementary. The frozen tables, ranking and candidate READMEs are hash-pinned
to the measured cohort and are unchanged, and both audits still pass
(`tools/check_final_evidence.py`, local and `--published-only`).

New sources live outside the frozen fingerprint scope. Haskell programs are
under `followup/src/` (compiled with `-ifollowup/src`), and external data under
`vendor-specs-followup/` ([manifest](../vendor-specs-followup/MANIFEST.md)).
`sourceFingerprint` hashes `src/`, `app/` and `vendor-specs/`, so adding files
there would have broken the frozen run's local audit.

| Open item (frozen report) | Status | Where |
| --- | --- | --- |
| Six native applications without completed vectors | Already done in the frozen cohort (121/121); the older report's stale paragraph is fixed | [NATIVE-PROTOCOLS-VALIDATION.md](NATIVE-PROTOCOLS-VALIDATION.md) |
| Every price an ESTIMATE without a C benchmark | **Done.** 21 bit-exact C sketches, benchmark-calibrated prices; ranks, tiers and fits unchanged | [C-BENCHMARKS.md](C-BENCHMARKS.md) |
| WOTS unrestricted worst path (30 compressions) unpriced | **Done.** 15,106 mWU worst path; 7,871 mWU for the 18-byte profile | [C-BENCHMARKS.md](C-BENCHMARKS.md) |
| Complete FROST transcript | **Done.** 14/14 vectors including RFC 9591 E.5; 3,830.371 WU | [below](#frost) |
| BN254 G1 addition and scalar multiplication (EIP-196) | **Done.** Exact precompile relations on go-ethereum vectors | [below](#bn254) |
| BN254 pairing check (EIP-197) | **Built and measured.** Exact relation, C-evaluator validated; 17.9M WU for one pair | [below](#pairing) |
| STARK wire compatibility | Compared against Stwo at a pinned commit; the hash difference is priced and it moves `blake2s_compress` | [below](#stark) |
| STARK security level | **Done.** 123 conjectured, 69.9 provable bits under ethSTARK v1.2 bounds | [below](#stark-security) |
| 1,595 eprint records deferred at metadata triage | **Done.** All re-triaged on full abstracts; none still deferred | [below](#eprint) |
| Verifiable timed signatures, concurrent blind-signing wrapper | Still open | [below](#still-open) |

## FROST

`followup-frost-secp256k1-transcript` is
[FrostTranscript.hs](../followup/src/JetDiscovery/Followup/FrostTranscript.hs).
It verifies a complete FROST(secp256k1, SHA-256) two-of-three signing
transcript. The frozen entry `eprint-frost-signature-share` took the binding
factor, challenge and Lagrange coefficient as operands; this program derives
them all in script:

- H4(msg) and H5(encoded commitment list);
- both binding factors H1(PK ‖ H4 ‖ H5 ‖ id): `hash_to_field` with
  `expand_message_xmd`(SHA-256), 48 bytes reduced modulo n using the existing
  scalar jets;
- the group commitment R = Σ (Dᵢ + ρᵢ Eᵢ), compressed;
- the challenge H2(R ‖ PK ‖ msg);
- both Lagrange coefficients from the identifiers (`scalar_invert`).

It then checks both signature shares, reusing the frozen `frostShareT`
relation, and the aggregate equation z·G = R + c·PK.

- **Reference.** The independent Integer reference reproduces RFC 9591
  Appendix E.5's published binding factors, group commitment and signature
  exactly.
- **Vectors: 14/14.** These are the RFC E.5 transcript, two derived signing
  sets (signers 1+2 and 2+3), and 11 rejections: tampered shares, swapped
  shares, a changed message, a negated commitment, unsorted commitments,
  identifiers 0 and 4, x = p, an off-curve x, and a share checked against
  another signer's key.
  [Log](data/followup-frost-transcript.txt).
- **Cost.** 3,830.371 WU under existing jets, 0.096% of `BUDGET_MAX`; program
  16,878 bits, witness 2,084 bits. It does not fit the fixed-stack scenario
  (2,495 WU; deficit 1,335.371 WU). No candidate jet matches. Removing the
  secp256k1 curve jets would raise it to 16.8M WU.
- **Bounds.** Exactly two signers out of three, a 4-byte message, the RFC E.5
  key set as policy constants. Commitments arrive as (y parity, x), so the
  SEC1 prefix is always well formed.

So a full FROST accountability check costs about 3.8 kWU on today's jets,
6.5× the frozen `eprint-frost-signature-share` relation (587.039 WU). That
relation checks one share with given factors; this program checks two
shares and the aggregate and derives every factor. FROST needs no new
primitive.

## BN254

[Bn254Precompiles.hs](../followup/src/JetDiscovery/Followup/Bn254Precompiles.hs)
checks a claimed EIP-196 output against its input. It enforces the
precompiles' rules: coordinates below p, (0, 0) as infinity, otherwise on
y² = x³ + 3, and a full 256-bit ECMUL scalar. Every exceptional case of
addition is handled. Field multiplication is Montgomery multiplication built
from `Arith.multiply word256`, which jet substitution lowers to existing
64-bit multiply jets. Inverses are witness hints checked by multiplication.
Vectors are go-ethereum's precompile tests at a pinned commit, normalised for
EVM calldata padding by `tools/bn254_vectors.py`. The Integer reference
reproduces all 35 expected outputs.

| Relation | Vectors | Native bound (WU) | Share of `BUDGET_MAX` | Fixed-stack scenario |
| --- | --- | ---: | ---: | --- |
| ECADD (0x06) | 20/20: 16 go-ethereum + 4 derived rejections | 9,330.693 | 0.23% | 1,554 WU; does not fit |
| ECMUL (0x07) | 22/22: 19 go-ethereum + 3 derived rejections | 2,590,845.587 | 64.8% | 9,363 WU; does not fit |

Logs: [ECADD](data/followup-bn254-ecadd.txt), ECMUL shards
`data/followup-bn254-ecmul-shard*.txt`.

**What the cost is made of.** `tools/gen_bn254_plain.sh` generates the same
relations with the field multiply replaced by the `bn254_fp_multiply`
candidate's specification (a·b mod p), so the overlay can price that jet
([log](data/followup-bn254-plain-whatif.txt); static cost, plus the first two
ECADD vectors as a check of the swap):

| Relation | Existing jets, Montgomery field | `multiply_256` overlay (frozen price) | `bn254_fp_multiply` overlay, frozen → benchmark price |
| --- | ---: | ---: | ---: |
| ECADD | 9,330.693 | 3,334.053 (78 uses) | 849.723 → ≈ 834 (12 uses) |
| ECMUL | 2,590,845.587 | 1,287,498.947 (16,953 uses) | 756,622.712 → ≈ 749,249 (5,642 uses) |

With a native field multiply, ECMUL still costs about 0.75M WU, 19% of
`BUDGET_MAX`. The residue is 256-bit modular addition, subtraction and
comparison, built from smaller-word jets on every one of 256 doubling and
addition steps. So a BN254 field-multiply jet alone does not make G1 scalar
multiplication cheap. The next bottleneck is wide modular add/sub. Two
candidate shapes follow, neither yet prototyped:

- a generic 256-bit `add_256`/`subtract_256` pair;
- a fused field `fp_add`/`fp_sub` for a given prime.

This strengthens the frozen report's point that field kernels need to be
judged together, not one multiply at a time.

## Pairing

[Bn254Pairing.hs](../followup/src/JetDiscovery/Followup/Bn254Pairing.hs) is
an exact EIP-197 pairing-check relation (precompile 0x08) for k pairs. It
checks a claimed 32-byte output (0 or 1) against the inputs, under the rules
of go-ethereum's current gnark backend (read at the vectors' commit):

- G1 canonical, (0, 0) = infinity, otherwise on the curve.
- G2 in EVM order (imaginary part first), canonical, all-zero = infinity,
  otherwise on the twist **and in the order-r subgroup**.
- Empty input returns 1. Pairs with an infinity factor contribute 1.

Construction:

- The Fp2/Fp6/Fp12 tower runs on the validated Montgomery field.
- An affine optimal-ate Miller loop over 6u+2 takes one inverse hint per step,
  checked as den·inv = 1, so a zero denominator rejects.
- The subgroup check computes (r−1)Q = −Q with the same hinted steps.
- The easy part of the final exponentiation uses an Fp12 inverse hint; the
  hard part is the Devegili–Scott–Dahab chain (three exponentiations by u).
- Each pair runs its own Miller loop. The k results are multiplied before one
  final exponentiation.

The independent Integer reference
([Bn254PairingRef.hs](../followup/src/JetDiscovery/Followup/Bn254PairingRef.hs))
passes all 14 go-ethereum pairing vectors, including the two expected-0 cases
and the 10-pair ones. Its hard part equals direct exponentiation by
(p¹²−1)/r exactly ([log](data/followup-bn254-pairing-reference.txt)).

**How it was validated.** The Haskell evaluator cannot hold this program
(about 60 GB for one exponentiation by u), and Haskell DAG construction
re-expands polymorphic operations at every use. So:

- The program is built from a generated monomorphic twin
  ([Bn254PairingDag.hs](../followup/src/JetDiscovery/Followup/Bn254PairingDag.hs),
  `tools/gen_bn254_pairing_dag.py`) that shares every closed operation once.
- It is executed by libsimplicity's own C evaluator
  ([bench/run_program.c](../bench/run_program.c)). The runner follows
  `simplicity_bitcoin_execSimplicity`, with no budget and the anti-DoS
  branch-coverage checks off, because these are unpruned research programs.
- On all 42 EIP-196 vectors the runner gives the same accept/reject outcome as
  the Haskell runs, and the same cost bound to the milliWU.
- Exact costs above libsimplicity's saturating 32-bit milliWU counter come
  from the corpus cost algebra on the same DAG.

**Components** ([log](data/followup-bn254-pairing-units.txt)). Each runs OK
against the Integer reference and fails with a wrong expected value:

| Component | Native bound (WU) |
| --- | ---: |
| Fp12 multiply | 37,402.213 |
| Fp12 square | 26,863.300 |
| Frobenius | 6,796.441 |
| Exponentiation by u | 2,668,478.423 |
| Final exponentiation | **8,800,685.310** (2.2× `BUDGET_MAX`) |

**Vectors.** Each go-ethereum vector is run with its correct claimed output
(must run OK) and with the output flipped (must fail):

| Pairs | Vectors (claimed output) | Correct output | Flipped output | Native bound (WU) | × `BUDGET_MAX` | Build memory |
| ---: | --- | --- | --- | ---: | ---: | ---: |
| 0 | `empty_data` (1) | OK | rejects | 7.534 | 0.000002 | — |
| 1 | `one_point` (0) | OK | rejects | 17,915,640.822 | 4.48 | 40 GB |
| 2 | `jeff1`, `jeff2`, `jeff3`, `two_point_match_2/3/4`, `ten_point_match_3` (1); `jeff6` (0) | 8/8 OK | 8/8 reject | 27,067,892.156 | 6.77 | 46–67 GB |
| 3 | `jeff4`, `jeff5` (1) | 2/2 OK | 2/2 reject | 36,220,143.490 | 9.06 | 75–77 GB |
| 10 | `ten_point_match_1`, `ten_point_match_2` (1) | 2/2 OK | 2/2 reject | 100,285,902.828 | 25.07 | 88–89 GB |

**All 14 go-ethereum vectors pass**, both expected-0 cases included
([results](data/followup-bn254-pairing-vectors-results.txt)). Programs with
the same number of pairs share one CMR across all their vectors, accepting and
rejecting alike ([CMRs](data/followup-bn254-pairing-cmrs.txt)), so the outcome
depends only on the witness. Each pair after the first adds 9,152,251.334 WU:
its own Miller loop, subgroup check and decoding. The 8,800,685.310 WU final
exponentiation is paid once.

**Reading the cost.** One pair costs 17,915,640.822 WU, 4.5× `BUDGET_MAX`.
The final exponentiation alone exceeds the maximum, so no BN254 pairing check,
and so no Groth16 verifier, fits on existing jets. Field arithmetic dominates:
one Fp12 multiply is 37.4 kWU. A `bn254_fp_multiply` jet removes most of the
multiply cost, but the measured G1 programs show modular add/sub then
dominating (see [BN254](#bn254)). A pairing within budget therefore needs
jetted tower arithmetic (an Fp12 multiply, or a whole pairing/Miller-loop
jet), or the residue-witness technique of
[2024/640](https://eprint.iacr.org/2024/640), which removes the final
exponentiation for accepting checks. This replaces the extrapolation in
[bn254-groth16.md](bn254-groth16.md) with a measured program.

Limits:

- Lines are multiplied as dense Fp12 elements.
- Per-pair Miller loops repeat the Fp12 squarings; a shared accumulator would
  avoid that.
- Exponentiation by u uses plain squaring; cyclotomic squaring would be
  cheaper.

All three overstate an optimised verifier, but not by the 4.5× needed to fit.

## STARK

### Wire compatibility with Stwo

The custom verifier ([FIBONACCI-STARK.md](FIBONACCI-STARK.md)) was compared
with StarkWare's Stwo, read as data at commit
`826591c6c371376810ca8213b5812d5daf6d5092` (default branch `dev`,
2026-08-13), files `crates/stwo/src/core/{fri.rs,pcs/mod.rs,vcs/blake2_merkle.rs}` and the module tree (`channel/blake2s.rs`, `poly/circle/`).

| Aspect | Custom verifier | Stwo |
| --- | --- | --- |
| Evaluation domain | multiplicative subgroup coset of CM31 | circle domain over M31 (canonic cosets) |
| First fold | binary fold `(a+b)/2 + β(a−b)/(2X)` | circle-to-line fold, then line folds (`fold_step`) |
| Last layer | constant | polynomial with `log_last_layer_degree_bound` |
| Commitments | SHA-256 binary Merkle; leaf = SHA-256 of 4 big-endian words | BLAKE2s Merkle (`blake2_merkle.rs`): node = BLAKE2s(left ‖ right ‖ little-endian column words); Poseidon252 variant for Cairo |
| Fiat–Shamir | SHA-256 transcript, counter-block query derivation | BLAKE2s or Poseidon252 channel (`channel/`) |
| Grinding | none | `pow_bits` proof of work before queries (default 10) |
| Lifting | none | `min_lifting_log_size` |

So the custom verifier is not Stwo wire-compatible. The incompatibility is
structural (domain and folding), not a serialisation detail.

**Pricing the hash difference.** A Stwo-compatible verifier would hash with
BLAKE2s. Stwo's `hash_node` hashes the two child hashes followed by any
column values committed at that layer (little-endian M31 words). An inner
node with no column values is a 64-byte input, that is one BLAKE2s
compression with the final flag set: the shape of the `blake2s_compress`
frontend. Nodes that carry column values, and leaves, can need more blocks.
The custom verifier's static path has 7,167 two-child node hashes (its
`sha256_pair` occurrences); leaf hashes are extra. Without a BLAKE2s jet, the measured corpus kernel
`xchain-blake2s-compress` costs 3,256.768 WU per compression, so node hashing
alone would be at least 23.3M WU, about 5.8× `BUDGET_MAX`. With
`blake2s_compress` at its benchmark price (1.033 WU), node hashing is about
7.4k WU, cheaper than today's two SHA-256 compressions per node.

**Effect on the recommendations.** The frozen ranking rejects
`blake2s_compress` because it matched only its own kernel. A Stwo-compatible
Bitcoin STARK verifier is a concrete, reusable demand for exactly that
frontend: column-free inner nodes always use the final-block shape. Leaves
and column-carrying nodes longer than 64 bytes need non-final blocks, which the
frozen frontend does not cover. If Stwo compatibility is a goal, move `blake2s_compress` from rejected
to at least maybe, with the non-final-block ABI as an open design question.
This is an ESTIMATE from measured kernels, not a measured Stwo verifier.

### STARK security

`tools/stark_security.py` applies the bounds of the ethSTARK Documentation,
Version 1.2 (July 2023; [vendored](../vendor-specs-followup/stark/ethstark-documentation-v1.2.pdf)
from StarkWare's Apache-2.0 `ethSTARK` repository) to the custom verifier's
parameters:

- |K| = (2³¹−1)⁴ ≈ 2^124.0;
- |D| = 2¹⁶ and rate 1/64;
- 48 queries, ten binary folds, no grinding;
- trace domain 2¹⁰ and d_max = 1,024;
- SHA-256 commitments, κ = 256.

Output: [data/followup-stark-security.json](data/followup-stark-security.json).

| Regime | Source | Bits |
| --- | --- | ---: |
| Conjectured security | Eq. (19): min{ζ + R·s, log₂\|K\|} − 1 | **123.0** (queries alone: 288) |
| Provable IOP knowledge soundness | Eq. (20), from Theorem 4 and the batched-FRI bound of BCIKS20 Thm 8.3 (Eq. 10), best m = 3 | **70.3** |
| Provable non-interactive (random-oracle) security | Corollary 3 with the §7.1.1 round-by-round terms, best m = 3 | **69.9** |

The binding term in both provable rows is the commit-phase proximity-gap term
(m + ½)⁷·n² / (c·ρ^{3/2}·|K|), at 2^−71.9 for the round-by-round constant
c = 3. The DEEP terms (2^−97.8 and below) and the query term (2^−133.3) are
far smaller. At this domain size, a 100-bit provable bound would need a
challenge field of about 2^154, for example a degree-5 extension of M31
instead of QM31. More queries do not help. Stwo states its own security as
`pow_bits + log_blowup_factor × n_queries` (`pcs/mod.rs`, `fri.rs`), which is
the conjectured regime.

Limits:

- These are the published ethSTARK bounds applied to this verifier's
  parameters, not a protocol-specific proof. The custom protocol differs from
  ethSTARK: no zero knowledge, a four-quotient Fibonacci AIR, and DEEP with
  four out-of-domain answers combined by powers of ρ.
- The 48 query positions are drawn independently, with collisions retained.
  That matches the theorem's s independent QUERY invocations.
- FRI tests degree below 1,024 while the honest DEEP polynomial has degree at
  most 1,022. The rate used above is the tested bound (1/64), so the slack is
  already accounted for.
- BCIKS20 itself (FOCS 2020; read from NSF's public-access copy,
  `https://par.nsf.gov/servlets/purl/10292832`) is IEEE-copyrighted and is
  not committed. The theorem used is the one restated as Theorem 3 in the
  vendored ethSTARK document.

## eprint

The frozen scan triaged 1,814 hits on search-result snippets and left 1,595
as DEFER. All 1,595 full eprint metadata pages (complete abstract, keywords,
category) are now vendored under
[vendor-specs-followup/eprint/abstracts/](../vendor-specs-followup/eprint/abstracts/manifest.json),
fetched rate-spaced, with a SHA-256 for each page. `tools/eprint_second_pass.py`
re-triages every one on the full abstract, asking what the corpus asks: must a
Bitcoin output verify something new in script, and if so, which primitive?

| Second-pass outcome | Records |
| --- | ---: |
| EXCLUDE: no in-script relation. Threshold decryption or keys 372, consensus 154, proof systems with no on-chain use 116, cryptanalysis 110, implementation 69, lattice non-signature 65, pairing non-signature 28, MPC/FHE 13, encryption 6, other 7 | 940 |
| MAPPED to a measured primitive family. Lattice signatures 75, pairing 75, proof verifiers 74, generic signatures 65, Schnorr 60, ECDSA 46, hash-based signatures 27, EdDSA 2 | 424 |
| Individually reviewed: every REVIEW (167), PQ-OTHER (57) and DEFER (7) row | 231 |
| Still DEFER | **0** |

[Rows](data/eprint-second-pass.tsv) and
[individual reviews](data/eprint-second-pass-reviewed.json). Of the 231
individual reviews:

- 123 exclude.
- 46 are scriptless or adaptor protocols whose on-chain objects are ordinary
  BIP340 signatures and timelocks.
- 34 are post-quantum signature families the corpus has not measured.
- The rest map to measured primitives.

**What the second pass found:**

- **No new in-script primitive outside the existing candidate families**, with
  two exceptions:
  - *Half-aggregated Schnorr* ([2022/222](https://eprint.iacr.org/2022/222))
    verifies with an n-term multi-scalar multiplication. Existing jets cover one
    term (`linear_combination_1`), and no candidate covers n terms. This is a gap
    worth prototyping if signature aggregation becomes a goal.
  - *Unmeasured post-quantum families* (34 reviewed records): isogeny (SQIsign,
    PRISM), multivariate (UOV, MAYO), code-based and MPC/VOLE-in-the-head. Their
    verifiers need large-prime isogeny arithmetic, small-field matrix
    arithmetic, or GGM-tree expansion, none of which the corpus measures.
- **Outside demand for ranked candidates.**
  [2024/1236](https://eprint.iacr.org/2024/1236) implements windowed
  big-integer multiplication in Script for BitVM field arithmetic, the work
  `multiply_256` and `bn254_fp_multiply` would replace. BitVM2 bridges
  (Clementine, [2025/776](https://eprint.iacr.org/2025/776)) and
  [2024/640](https://eprint.iacr.org/2024/640) need the BN254 pairing.
- **Two time-lock-puzzle papers** ([2023/1024](https://eprint.iacr.org/2023/1024),
  [2020/1078](https://eprint.iacr.org/2020/1078)) join the open
  verifiable-timed-signatures item.
- **FlatMerkle** ([2026/2717](https://eprint.iacr.org/2026/2717),
  [2026/2468](https://eprint.iacr.org/2026/2468)) verifies data published on
  Bitcoin by SHA-256 midstate continuation, which the existing `sha_256_ctx_8`
  jets already express.

**Accuracy.** A random audit of 50 automated verdicts
([record](data/eprint-second-pass-audit.json)) found 2 misses: two
MPC-in-the-head signature components excluded as proof systems. Their family is
already flagged, so no primitive family is missed. Seven rows (14%) were in the
wrong category, mostly MAPPED where EXCLUDE was right, and about ten more had an
imprecise reason label. So the pass answers the primitive question reliably,
but its per-family MAPPED counts are approximate. Classification reads full
abstracts, not full papers; a paper whose abstract hides its on-chain relation
can still be missed. 143 of the individual reviews rest on titles, keywords
and the automated abstract rules; 88 rest on a reading of the full abstract
(see each entry's `basis` field).

## Still open

- **Verifiable timed signatures** (eprint 2020/1563, VT-Schnorr Figure 3).
  Unchanged from [timed-signatures.md](timed-signatures.md). The verifier
  needs range proofs and linearly homomorphic time-lock puzzles over a
  composite modulus: thousands-of-bits modular exponentiation for which no
  corpus kernel or candidate exists. Setup, modulus size and repetition count
  must be fixed first.
- **Concurrent blind-signing wrapper** (eprint 2022/1676). The single-session
  algebra is measured. The concurrency machinery (NIZK plus PKE) is an
  off-chain wrapper whose on-chain cost depends on a proof system that has not
  been chosen.
- **Unmeasured post-quantum signature families** surfaced by the eprint second
  pass: isogeny (SQIsign, PRISM), multivariate (UOV, MAYO), MPC/VOLE-in-the-head
  and HAWK. Each needs primitives the corpus has not measured.
- **Period-ranking access gaps** ([PERIOD-RANKINGS.md](PERIOD-RANKINGS.md)):
  unchanged; the blocked sources still need manual access.
