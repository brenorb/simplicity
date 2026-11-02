# Candidate: `p256_ecdsa_verify` — ECDSA verification over secp256r1 (P-256)

## Type signature
`((Word256 qx_or_compressed, Word256 msg_hash), (Word256 r, Word256 s)) -> ()` (asserting, like `bip_0340_verify`)

## Specification
FIPS 186-5 ECDSA verification over P-256 (as in Ethereum's RIP-7212 / EIP-7951 precompile `P256VERIFY`).
No Simplicity reference expression is written here: a P-256 field, group and scalar library in Simplicity is the
large piece of work this candidate would avoid, and the proxy measurements below already settle the jet granularity.

## Cost (ESTIMATE)
2 x `Bip0340Verify` = 98.842 WU. Method: P-256 has no GLV endomorphism and generic implementations are slower
than libsecp256k1's; a factor of 2 over secp256k1 verification is a deliberately pessimistic placeholder until a C
implementation is benchmarked.

## Corpus evidence (proxy measurements, secp256k1 code structure)
`reports/ablations.md` re-costs the secp256k1 programs with jet families removed. These are measurements of
secp256k1 code; they are used as a structural proxy for what P-256 would cost at each jet granularity:
- With field and scalar jets but no curve-level jets, one BIP 340 verification (`bip348-csfs-32`) costs
  2,400,794.758 WU, 60% of `BUDGET_MAX`. Two verifications (`app-multisig-2of3`, three keys) cost 7,202,394.792 WU
  and exceed `BUDGET_MAX`.
- With no secp256k1 jets at all (word jets only), one verification costs 969,195,266.403 WU (242x `BUDGET_MAX`).
So a P-256 jet set of field operations alone would not make P-256 verification usable; a curve-level jet
(`p256_ecdsa_verify`, or a `p256_linear_verify` analogous to `linear_verify_1`) is required.

## Generality
Passkeys / WebAuthn, secure-element and HSM keys, TLS/X.509 signatures, Ethereum's P256VERIFY. Demand is shown by
Ethereum adding it as a precompile.

## Verification burden
High. A new curve: the secp256k1 field and group proofs (fe_multiply with u128 oracles, gej_ge_add_ex, the secp
symbolic executor on the jet-equivalence work) give a template, but P-256's prime needs its own reduction proofs, and
the C implementation would be new code outside libsecp256k1.

## Alternatives considered
- P-256 field jets only: measured above to be insufficient.
- A generic modular-arithmetic family (`mod_mul_256` with a modulus input): more general, but curve arithmetic built
  on it would still face the curve-level cost shown above.
