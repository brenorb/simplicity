# Elements output-nonces C-to-Simplicity proof

Private tree: `/private/tmp/jet-elements-nonces.mniejwp9`, forked from the
completed, immutable `elements-outpoints` tree. No normal registry, canonical
source, production C/header or inherited proof is changed.

`RUN.json` records fresh Coq 8.17.1 compilation and full contracts/assumptions
for three modules, eleven results and twelve definitions. Nine results are
closed; the hash-loop semantics uses inherited functional extensionality;
the complete C endpoint uses the existing six inherited assumptions.

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

`CHECKED.json` records the successful recursive kernel/AST phase under
handle96093 (terminal exit zero). The original Elements AST regenerates
exactly; the recursive context matches the existing fifteen-axiom library
profile, with no unsafe kernel features. This library-wide context is distinct
from the six inherited assumptions of the individual C endpoint.
The source-fidelity review and all59 targeted source-corruption tests also
passed. The independent evidence reconciliation passed under handle30568;
the full evidence-review finish then completed under handle32533, with all59
proof/kernel/command/source/report/object/dependency corruptions rejected.
`EVIDENCE-REVIEW.json` binds the completed receipts, tools, logs and unchanged
private sources. This is still an unregistered isolated proof package.

The checked private input fingerprint is
`0d090ba6b09dfa408a0df69674582d6278d14e77f7225557d9693927e4864a28`.
No caller-cache construction, normal registration or full acceptance is
implied by this isolated proof checkpoint.

Reproduction (the drivers refuse to overwrite completed receipts):

```sh
python3 -B proof-work/elements-nonces/check.py /private/tmp/jet-elements-nonces.mniejwp9
python3 -B proof-work/elements-nonces/kernel.py /private/tmp/jet-elements-nonces.mniejwp9
```

All three archived `.v.source` files compile completely through their final
`Qed`. Earlier interactive failure logs are debugging history, not evidence
that an incomplete proof was accepted. The parametricity fix prioritizes
`Word.zero_Parametric` before constructor automation unfolds the zero program.
