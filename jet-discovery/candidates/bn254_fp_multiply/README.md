# Candidate: `bn254_fp_multiply`

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
