# Candidate: `bn254_fp_multiply`

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: The measured base- and extension-field kernels show substantial local savings and a plausible BitVM proof path. Benchmark canonical input and output conversion before valuing a pairing verifier; only the dense multiplication component is modeled.

Price: **1.626 WU (ESTIMATE)**. ESTIMATE: 2 x FeMultiply for a generic 254-bit Montgomery reduction; requires an implementation and benchmark

Matches in 2 of 157 registered rows: 2 matched DAG nodes across all branches, 4 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| eprint-bn254-fp-multiply | kernel | 1 | 1 | 3,867.295 | 66.685 | 3,800.610 | yes / yes at 4627 WU |
| eprint-bn254-fp2-multiply | kernel | 3 | 1 | 11,821.680 | 419.850 | 11,401.830 | no / yes at 4850 WU |

See the [complete matrix](../../reports/candidate-ranking.md#bn254_fp_multiply) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

Type: `(Word256, Word256) -> Word256`.

The specification is `(a*b) mod p`, with
`p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`
(the BN254 base field, not its scalar field). The Simplicity reference expression
is `JetDiscovery.Corpus.BN254.fpMul`: exact 256-by-256 multiplication followed
by 512-bit `div_mod`, returning the low 256 bits of the remainder. It accepts
arbitrary 256-bit inputs; the corpus wrappers additionally check canonical
operands. `fp2MulRef` is an independent Integer reference for extension arithmetic.

The what-if registry prices this at **ESTIMATE: 2 × the existing `FeMultiply`
benchmark**, to allow a generic 254-bit Montgomery reduction. This is an analogy,
not a benchmark of BN254 C code. A real implementation could change that ratio.

The extension-field expression composes three base-field products using
Karatsuba over `u²=-1`. The reference tests compare the expression to Haskell
Integer multiplication and modular reduction. The pre-final validation passed
all 12 base and extension field vectors, including zero, maximal canonical
operands, a 253-bit carry case, and incorrect-result rejection.
[Scoped validation and pairing extrapolation](../../reports/bn254-groth16.md)

BN254 is useful beyond one opcode: Groth16 bridge verifiers, pairing relations,
G2 arithmetic and proof systems used by BitVM bridges. This reverses the earlier
exclusion based on lack of a Bitcoin deployment path. [BitVM2](https://eprint.iacr.org/2025/1158)
and [On Proving Pairings](https://eprint.iacr.org/2024/640) support the Bitcoin
bridge use. [eprint 2024/1498](https://eprint.iacr.org/2024/1498) supplies an
arithmetic comparison, but its deployment claim is explicitly BSV and is not
used as evidence of Bitcoin mainnet compatibility.

Verification burden is **medium to high (judgement)**. The proven
`fe_multiply` work on `feat/jet-equivalence` gives a multiplication/reduction
proof pattern, but its secp256k1 modulus and representation cannot be reused as
BN254 semantics. A new C implementation, bounds/carry proof, canonical-output
proof and total-input specification agreement are required. Generic
`multiply_256` and `div_mod_512` candidates are more general alternatives;
a full pairing jet would save more plumbing at a much larger proof burden.
This prototype does not alter any consensus jet map or cost.
