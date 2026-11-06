# BN254 and Groth16: measurement versus extrapolation

The corpus measures two actual Simplicity expressions:
`eprint-bn254-fp-multiply` and `eprint-bn254-fp2-multiply`. The former uses
exact 256-by-256 multiplication and 512-bit modular division; the latter
uses three such multiplications in a Karatsuba product over `u² = -1`.
Both validate canonical operands and check the computed result against an
independent Haskell Integer reference. The frozen full cohort passed all 12
vectors (7 Fp and 5 Fp2). It measured the native bounds and applied the
hypothetical Fp candidate in isolation, leaving the outer wrappers unchanged.
A separate typed-arrow measurement removes those wrappers.

| Expression | Actual native bound (WU) | Selected Fp matches | Isolated Fp overlay (WU, ESTIMATE) |
| --- | ---: | ---: | ---: |
| Fp corpus entry, including wrapper | 3,867.295 | 1 | 66.685 |
| Fp2 corpus entry, including wrapper | 11,821.680 | 3 | 419.850 |
| Bare Fp arrow | 3,802.336 | 1 | 1.726 |
| Bare Fp2 arrow | 11,688.558 | 3 | 286.728 |

The overlay price is 1.626 WU from twice the in-tree `FeMultiply` benchmark,
plus the cost algebra's 0.100 WU jet overhead per call. Bare-arrow overlay
values are derived from that price and reconcile with the two observed
same-context overlays. See the exact [Fp replay](data/isolated-final-157-lf/eprint-bn254-fp-multiply-attempt1.txt),
[Fp2 replay](data/isolated-final-157-lf/eprint-bn254-fp2-multiply-attempt1.txt),
[typed-arrow log](data/bn254-typed-kernel-costs.txt), and
[final model record](data/bn254-groth16-estimate.json). The wrapped results
agree with the [standalone measurements](data/bn254-pre-final-measurements.json).
No Groth16 verifier was run or counted.

The deployment path is Bitcoin bridge verification/disputes, documented by
[BitVM2](https://eprint.iacr.org/2025/1158) and
[On Proving Pairings](https://eprint.iacr.org/2024/640). The latter discusses
BN254 and replacing final exponentiation with a residue check, and observes
that two of Groth16's three pairing second arguments can be fixed. The
comparison paper [2024/1498](https://eprint.iacr.org/2024/1498) targets BSV;
it is not evidence that its script runs unchanged on Bitcoin.

## Explicit ESTIMATE scenario

The following deliberately naive **ESTIMATE arithmetic component** makes the
extrapolation reproducible without disguising it as a measured verifier.
Use the [EIP-197](https://eips.ethereum.org/EIPS/eip-197) base prime `p`,
subgroup order `r`, and extension field. A Groth16 check with a precomputed
`e(alpha,beta)` target has three variable pairing terms.

| Quantity | Arithmetic model | Count |
| --- | --- | ---: |
| BN curve parameter | `u = 4965661367192848881` | fixed |
| Binary optimal-Ate loop | `k = 6*u+2`; bit length 65; popcount 37 | 64 doublings, 36 additions |
| Shared Miller accumulator squarings | one per remaining bit | 64 |
| Dense line multiplications | three pairings × (64 double lines + 36 add lines + 2 Frobenius correction lines) | 306 |
| Generic binary final exponentiation | `E = (p^12-1)/r`; bit length 2790; popcount 1376 | 2789 squares + 1375 multiplies = 4164 |
| Dense Fp12 operations | `64+306+4164` | 4534 |
| Schoolbook Fp12 multiplication | degree-five polynomial over Fp2, 36 coefficient products + 5 reductions by `(9+i)` | 41 Fp2 multiplies |
| Fp2 multiplication | Karatsuba with `i²=-1` | 3 Fp multiplies |
| Base-field multiplication component | `4534*41*3` | 557682 |

Here `i` is the quadratic extension indeterminate. The script checks the
BN polynomial identities for `p` and `r` against the curve parameter in the first row. All squarings are pessimistically
charged as general multiplications; all line products are pessimistically
charged as dense products. A production implementation uses sparse
multiplication, special squaring, signed-digit loops, Frobenius maps,
fixed-key precomputation and/or residue checks. The source of the loop
structure is the standard optimal-Ate algorithm, also visible in
[go-ethereum's reference implementation](https://github.com/ethereum/go-ethereum/blob/master/crypto/bn256/cloudflare/optate.go).
No source from that implementation is compiled or executed here.

| Dense arithmetic scenario | Count × unit | Arithmetic component (WU, ESTIMATE) |
| --- | ---: | ---: |
| Native Fp multiplication only | 557,682 × 3,802.336 WU | 2,120,494,345.152 |
| Native Fp2, including its internal additions/subtractions | 185,894 × 11,688.558 WU | 2,172,832,800.852 |
| Hypothetical Fp jet calls only | 557,682 × 1.726 WU | 962,559.132 |

The rows are alternative cost models. In particular the third row excludes
all additions/subtractions; it cannot be used to infer an overall speedup or
that a Groth16 spend would fit. All three omit G2 line-coefficient generation,
G1 public-input MSM, Fp12 coefficient additions, point validation/subgroup
checks and encoding. Dense assumptions overprice operations a real pairing
can optimize, while omissions underprice the remaining work. The estimates
therefore bound neither side of the cost of an optimized full pairing check.

Reproduce the [final model](data/bn254-groth16-estimate.json) with the same
frozen runner from the terminal cohort manifest:

```bash
python3 tools/bn254_extrapolate.py --runner <same-frozen-runner>
```

The script rejects a stale run fingerprint or failed/incomplete BN254
results and reconciles wrapped and bare costs. The separate `--pre-final`
mode reproduces the [standalone packet](data/bn254-groth16-pre-final-estimate.json)
using its saved logs and snapshots. To repeat the local measurements,
build the project as in [METHOD.md](METHOD.md)
and run the built runner with `run eprint-bn254 +RTS -N1 -A16m -M8G -s -RTS`.
Compile the standalone `tools/BN254KernelCost.hs` against the in-tree package
via the local `dist-newstyle/packagedb/ghc-<version>` and `-isrc`, with an
ignored output directory and `-rtsopts`; use the same RTS flags for that binary.

## Candidate decision

[`bn254_fp_multiply`](../candidates/bn254_fp_multiply/README.md) is a reusable
primitive candidate, priced only by an explicitly labelled benchmark
analogy. The measured kernels support investigating it; two kernel rows
do not justify a monolithic pairing jet or establish corpus frequency for
full bridges. The candidate and generic `multiply_256` / `div_mod_512`
alternatives should be compared after implementing an optimized complete
verifier.
