# Candidate: `bn254_fp_multiply`

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

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

The two complete pre-final measurements found one exact occurrence in
`eprint-bn254-fp-multiply` and three in `eprint-bn254-fp2-multiply` (Karatsuba
over `u²=-1`). Their isolated bounds fell from 3,867.295 to 66.685 WU and
11,821.680 to 419.850 WU respectively, savings of 3,800.610 and 11,401.830 WU
(**ESTIMATE**). Both are arithmetic entries; they do not establish full spend
feasibility. The normal tests compare the expression to Haskell Integer
multiplication and modular reduction. All 12 corpus vectors pass, including
zero, maximal canonical operands, a 253-bit carry case and incorrect-result
rejection. See [measurements and extrapolation](../../reports/bn254-groth16.md)
for the complete measured scope. The complete run reports whole-corpus impact separately.

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
