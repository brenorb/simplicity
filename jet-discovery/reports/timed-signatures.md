# Verifiable timed signatures: exact remaining path

**Not implemented; no corpus program or WU claim.** The concrete target is
VT-Schnorr, Figure 3, in the authors' [paper](https://verifiable-timed-signatures.github.io/web/assets/paper.pdf)
(November 13, 2020 version; related [eprint 2020/1563](https://eprint.iacr.org/2020/1563)).
Its verification requires four checks:

| Required path | Present corpus support | Still missing |
| --- | --- | --- |
| Interpolated public-key and nonce-share consistency | secp256k1 arithmetic and scalar jets | bounded full share-set interpolation and validation |
| Every encrypted share's range proof | generic word/hash arithmetic | complete section 4.5 range-proof verifier |
| Opened puzzles regenerated from disclosed shares/randomness; Schnorr share equations | Schnorr linear relations measured elsewhere | linearly homomorphic time-lock puzzle generation/checks over the composite modulus |
| Fiat–Shamir selected opening set | SHA-256/transcript building | exact Figure 3 transcript encoding, challenge-to-subset mapping, proof generation and negative vectors |

A complete implementation must bind all four checks to the same message,
public key, puzzle parameters and commitments. CLTV/CSV does not establish
any of these encrypted-signature guarantees. The missing work is a verifier
implementation, not evidence that Simplicity lacks expressiveness. Setup,
modulus size, repetition count and transcript encoding must be fixed before
measurement. The authors' PDF is vendored as data, with its distinct revision
and licensing status recorded in the source manifest; downloaded code is not run.
