# C benchmarks of the candidate jets

**All 21 executable candidate frontends now have a standalone C sketch that
reproduces its Simplicity reference expression bit for bit on 8,442 generated
vectors.** Timing them beside 21 existing libsimplicity jets gives
benchmark-calibrated prices. They replace the analogy ESTIMATEs as the best
available price, but they are still **ESTIMATES**: the sketches are not
consensus code, and this machine is not the one behind `rawBenchmark`.

What changed:

- Arithmetic candidates cost 2–6 times less than their frozen estimates. For
  example, `p256_fe_multiply` is 374 mWU, not 1,219, and `div_mod_512` is 464,
  not 2,704.
- Most hash compressions land close to the SHA-256 analogue. BLAKE2s (×1.35),
  RIPEMD-160 (×1.25) and BLAKE3 (×1.15) cost more than estimated; Keccak is
  slightly cheaper (×0.91).
- The open WOTS item is now priced. The unrestricted worst path of
  `sha256_wots_chain_16` (30 compressions) costs **15,106 mWU**. The matched
  18-byte-buffer profile (15 compressions) costs **7,871 mWU**, and the
  fixed-prefix frontend **7,469 mWU**.
- First-order re-scoring with these prices keeps every family's rank and every
  strong/maybe/rejected tier. No budget-applicable program changes its
  fixed-stack fit. Savings are dominated by what a candidate replaces, not by
  the candidate's own price.

The frozen [RECOMMENDATIONS.md](RECOMMENDATIONS.md) and candidate READMEs are
hash-pinned to the measured cohort, so they are unchanged. This report
supplements them.

## Method

1. **Reference vectors.** `tools/CandidateCVectors.hs` evaluates each
   registered candidate's reference expression on 402 inputs. The inputs are
   all-zero, all-ones, and 400 drawn per word from these families: uniform,
   zero, all-ones, small, near a power of two, and near each relevant modulus
   (M31, KoalaBear, ed25519, P-256 p/n, BN254, secp256k1 p/n). It writes Bit
   Machine input and output cells with a padding mask. The output is
   [data/candidate-c-vectors.tsv](data/candidate-c-vectors.tsv).
2. **Sketches.** `candidates/<name>/sketch.c` reads and writes frames exactly as
   a libsimplicity jet does, and returns false where the reference fails. Where
   the reference has total word semantics (non-canonical field inputs, wrap
   behaviour), the sketch follows the same operation sequence. `bench verify`
   checks every vector: **21/21 PASS**, including the 204 rejecting
   `sha256_wots_chain_16` vectors (overflowing SHA-256 contexts).
3. **Timing.** `bench/` compiles the unmodified in-tree `frame.c`, `jets.c`,
   `jets-secp256k1.c` and `sha256.c` into an ignored build directory. It uses
   `-O2 -DPRODUCTION`, the optimisation the nix C wrapper gives the upstream
   build. Sketches and the existing jets go through one function-pointer loop.
   Each input's figure is the median of 7 repetitions, each at least 2 ms long.
   Panel jets use 32 uniform random inputs. LinearCombination1 and Decompress
   use a valid point, because they reject random ones before doing their work.
   Machine: [data/candidate-c-bench-machine.txt](data/candidate-c-bench-machine.txt)
   (Apple M5 Max, arm64, Apple clang 21). Output:
   [data/candidate-c-bench.tsv](data/candidate-c-bench.tsv).
4. **Calibration.** `tools/bench_prices.py` fits `rawBenchmark = a + s·t` over
   the panel, minimising relative error. The fit is a = 37.5 raw units and
   s = 2.362 raw/ns. The intercept absorbs per-call overhead that the upstream
   harness has and this loop lacks. Prices are `WU = raw · 100 /
   rawBenchmark("CheckSigVerify")`, the normalisation of
   `Simplicity.Bitcoin.Benchmarks.cost`.
5. **Worst case.** A jet is charged its worst case. Each sketch is priced at the
   95th percentile of its per-input times; the maximum is reported but is mostly
   timer noise for constant-time code. Both WOTS chains depend on the start
   index, so they are priced at start = 0 from a regression of time on
   compressions performed. For the generic chain that is 15 steps with a buffer
   of at least 36 bytes (2 compressions per step), confirmed by 9 observed
   30-compression vectors at up to 3,525 ns.

### Calibration accuracy

Leave-one-out relative error over the 21-jet panel: **median 8.7%, maximum
38.8%**. The fit is tight across the size range of most candidates
(Sha256Block −3.0%, FeMultiply +1.9%, ScalarNormalize +3.5%). It is loosest
for the smallest jets (Multiply64 +38.8%, DivMod128_64 −35.9%), where per-call
overhead dominates, and for the largest (LinearCombination1 −33.3%). Treat
prices of the tiny arithmetic candidates (`koalabear_add`, `m31_mul`,
`multiply_128`) as uncertain by roughly ±40%, and the others by roughly ±20%.
Full table: [data/candidate-bench-calibration.tsv](data/candidate-bench-calibration.tsv).

## Prices

`bench` is the calibrated price used below. `analogue` scales instead by the
jet the frozen estimate was built from: `raw_ref · t / t_ref`. The gap between
the two is a second measure of calibration uncertainty. Both are mWU,
**ESTIMATE**.

| candidate | frozen ESTIMATE | bench | analogue | bench / frozen | p95 ns |
| --- | ---: | ---: | ---: | ---: | ---: |
| `blake2b_compress` | 1,147 | 1,233 | 1,319 | 1.07 | 271.0 |
| `blake2s_compress` | 765 | 1,033 | 1,093 | 1.35 | 224.6 |
| `blake3_compress_cv` | 535 | 616 | 620 | 1.15 | 127.4 |
| `bn254_fp_multiply` | 1,626 | 319 | 269 | 0.20 | 58.4 |
| `div_mod_256` | 676 | 260 | 761 | 0.38 | 44.6 |
| `div_mod_512` | 2,704 | 464 | 1,573 | 0.17 | 92.2 |
| `ed25519_fe_multiply` | 813 | 233 | 177 | 0.29 | 38.4 |
| `keccak_f1600` | 1,530 | 1,397 | 1,505 | 0.91 | 309.2 |
| `koalabear_add` | 179 | 84 | 92 | 0.47 | 3.7 |
| `m31_mul` | 174 | 86 | 60 | 0.49 | 4.1 |
| `multiply_128` | 288 | 132 | 175 | 0.46 | 14.9 |
| `multiply_256` | 1,152 | 236 | 458 | 0.20 | 39.0 |
| `p256_fe_multiply` | 1,219 | 374 | 327 | 0.31 | 71.1 |
| `pubkey_unpack_neg` | 656 | 130 | 85 | 0.20 | 14.4 |
| `qm31_mul` | 813 | 205 | 146 | 0.25 | 31.8 |
| `ripemd160_compress` | 765 | 954 | 1,004 | 1.25 | 206.2 |
| `sha256_pair` | 1,530 | 1,503 | 1,625 | 0.98 | 334.0 |
| `sha256_wots_chain_16` (worst, 30 compressions) | 11,475 | 15,106 | 15,859 | 1.32 | 3,499 (regression) |
| `sha256_wots_chain_16` (18-byte profile, 15 compressions) | 11,475 | 7,871 | — | 0.69 | 1,816 (regression) |
| `sha256_wots_chain_16_fixed` (start 0) | 11,475 | 7,469 | 8,390 | 0.65 | 1,722 (regression) |
| `sha512_compress` | 1,147 | 1,204 | 1,286 | 1.05 | 264.3 |
| `signature_unpack` | 1,156 | 223 | 212 | 0.19 | 36.0 |
| `ecrecover` | 107,232 | 107,099 | — | 1.00 | — |

The division sketches use Knuth's algorithm D on 64-bit limbs. Their
`analogue` column is high because DivMod128_64 is an overhead-dominated tiny
jet, the panel's worst-fitting point.

`ecrecover` keeps its frozen sum of existing secp256k1 jet benchmarks, with
the Keccak proxy (2 × Sha256Block) replaced by the measured `keccak_f1600`.
`secp256k1_ecdsa_verify` is already a sum of existing benchmarks; it has no
sketch, and its frozen price and stated omissions are unchanged.

Raw prices, with per-candidate method text:
[data/candidate-bench-prices.tsv](data/candidate-bench-prices.tsv).

## Effect on the recommendations

`tools/bench_prices.py` re-scores the frozen isolated-impact matrix with the
frozen ranking policy (context weights, generality, burden, one row per family
and counting group). Each row's repriced bound is
`isolated + occurrences × (bench − frozen)`, using the occurrences on the
frozen worst path. This is exact while that path stays the worst. A cheaper
price can let another path dominate, so the savings shown are upper bounds
where a price fell. Rows with zero selected occurrences keep their frozen
saving. Output: [data/candidate-ranking-bench.json](data/candidate-ranking-bench.json).

- **Rank order is unchanged for all 22 families.** Scores move by at most 2.8% (`koalabear_add`; under 1.2% for every other family),
  because a candidate's saving is the cost of the Simplicity expression it
  replaces, which is far larger than the jet's own price.
- **No fixed-stack fit changes.** No budget-applicable row crosses its budget
  in either direction. In particular:
  - The stateless SHRINCS and SLH-DSA-128s programs keep fitting with the
    fixed-prefix chain, now with more margin.
  - The stateful SHRINCS program uses the generic chain on 32 occurrences.
    It does not fit at either generic WOTS price: about 8.45 kWU at the
    worst-path price and about 8.22 kWU at the 18-byte-profile price, against
    a 3,933-WU budget.
- The STARK margins in [FIBONACCI-STARK.md](FIBONACCI-STARK.md) grow, because
  `qm31_mul` is cheaper (205 vs 813 mWU across 5,066 occurrences). The
  isolated `m31_mul` overlay still does not fit.

So the tiers in RECOMMENDATIONS.md stand. Burden and generality, not price,
decide between candidates with similar savings.

## Limits

- **Different machine.** `rawBenchmark` was measured upstream on unstated
  hardware. This is arm64 with libsimplicity's portable SHA-256 (no SHA-NI),
  and the affine calibration is the only bridge. A consensus price needs the
  upstream benchmark harness on the reference machine.
- **Sketches are not production jets.** They are straightforward, not
  constant-time, and not tuned (no vectorised Keccak/BLAKE, no assembly field
  arithmetic). A tuned jet would usually be cheaper, so these prices lean
  high for hashing. Frame I/O is real libsimplicity code and is included.
- **Coverage.** Random vectors almost never reach algorithm D's rare add-back
  step, so that branch of the division sketches is unexercised. It affects
  correctness of a rare path, not the price.
- **First-order re-scoring.** The overlays were not re-run with the new
  prices. Re-running them would cost a full corpus run (hours, tens of GiB).
  The bound direction is stated above.

## Reproduce

From `jet-discovery/`:

```sh
nix-shell --run 'ghc -O1 -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery -outputdir /tmp/ccv tools/CandidateCVectors.hs -o /tmp/ccv/ccv'
/tmp/ccv/ccv 400 > reports/data/candidate-c-vectors.tsv     # deterministic, about 1.5 h
make -C bench verify                                         # 21/21 PASS
JD_PER_INPUT=1 bench/build/bench bench reports/data/candidate-c-vectors.tsv > reports/data/candidate-c-bench.tsv
python3 tools/bench_prices.py reports/data/candidate-c-bench.tsv
```

Timings vary by machine; the calibration and the bench/frozen ratios are what
carry over.
