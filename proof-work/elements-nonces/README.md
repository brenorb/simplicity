# Elements output-nonces C-to-Simplicity proof

The endpoint `elements_output_nonces_hash_program_local_spec` proves the
original `f_simplicity_output_nonces_hash` in `elements_ge` against a
primitive-based Simplicity nonce-hash loop. It reuses the existing complete
getter/call/allocation/free/framing proof, not an assumed execution. The
canonical program iterates over `OutputNonce` with the verified 32-bit
`forWhile` and finalizes SHA-256 on either loop exit. The proved serializer
keeps these cases distinct:

- absent output: terminate the loop;
- present output, absent nonce: absorb byte zero;
- confidential nonce: absorb prefix 2/3 and all 32 payload bytes;
- explicit nonce: absorb prefix 1 and all 32 payload bytes.

Nonce payloads are native Word256 values, not range-restricted field elements.
The shared `ctx8_tagged_word_spec` lemma factors prefix-byte plus payload
absorption, for later confidential serializers as well as nonce hashing.

Boundary: `hash_getter_rep` explicitly relates the cached transaction hash at
offset 56 in the 760-byte structure to the logical hash. This package does
not establish that relation from the actual transaction builder. Caller
frame/representation conditions remain explicit; no overlapping-buffer API
claim, host-library equivalence or assertion-enabled-build claim is added.
Canonical source-fidelity review, recursive kernel checking and normal
registration are separate stages, not implied by compilation. Coverage added:
zero until the admission workflow is complete.

## Completed verification

The checked private input fingerprint is
`0d090ba6b09dfa408a0df69674582d6278d14e77f7225557d9693927e4864a28`.
No caller-cache construction, normal registration or full acceptance is
implied by this isolated proof checkpoint.

Reproduction (the drivers refuse to overwrite completed receipts):

All three archived `.v.source` files compile completely through their final
`Qed`. Earlier interactive failure logs are debugging history, not evidence
that an incomplete proof was accepted. The parametricity fix prioritizes
`Word.zero_Parametric` before constructor automation unfolds the zero program.
