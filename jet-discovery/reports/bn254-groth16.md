# BN254 and Groth16: measurement versus extrapolation

The corpus measures two actual Simplicity expressions:
`eprint-bn254-fp-multiply` and `eprint-bn254-fp2-multiply`. The former uses
exact 256-by-256 multiplication and 512-bit modular division; the latter
uses three such multiplications in a Karatsuba product over `u² = -1`.
Both validate canonical operands and check the computed result against an
independent Haskell Integer reference. Their costs, vector outcomes and
what-if overlays are in [corpus-results.md](corpus-results.md) and
[whatif.md](whatif.md). Those are measurements; no full Groth16 verifier has
been implemented or counted.

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

Reproduce the integer counts and multiply by the measured field-kernel
unit (including its validation/equality wrapper) with:

```bash
python3 tools/bn254_extrapolate.py > reports/data/bn254-groth16-estimate.json
```

The script refuses to produce a cost if the regenerated runner TSV lacks
the BN254 row or its vectors failed. The resulting WU figure is labelled
**ESTIMATE**. It excludes G2 line-coefficient generation, G1 public-input
MSM, additions/subtractions, point validation/subgroup checks and encoding.
It is therefore neither an upper bound nor a lower bound on a complete
optimized pairing check. The only defensible next step toward an actual
Groth16 number is to implement and measure that complete path. In
particular, multiplying the Fp kernel cost by an unstated constant would
not establish Groth16 feasibility.

## Candidate decision

[`bn254_fp_multiply`](../candidates/bn254_fp_multiply/README.md) is a reusable
primitive candidate, priced only by an explicitly labelled benchmark
analogy. The measured kernels support investigating it; two kernel rows
do not justify a monolithic pairing jet or establish corpus frequency for
full bridges. The candidate and generic `multiply_256` / `div_mod_512`
alternatives should be compared after implementing an optimized complete
verifier.
