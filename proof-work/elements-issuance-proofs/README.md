# Elements issuance_range_proofs_hash: reuse the two-primitive reader loop

Private tree: `/private/tmp/jet-elements-issuance-proofs.OurYz6Pe`, cloned from
the completed outpoints proof tree. No live audit objects or main inputs were
modified. The user's original staged patch remains preserved.

The archived source proves `f_simplicity_issuance_range_proofs_hash` against
the literal Elements program with separate IssuanceAssetProof and
IssuanceTokenProof primitive lookups, both early exits, a64-byte absorber and
the32-bit counter loop. A formal body/program equality lets it reuse the
existing generic SHA element-reader loop, rather than enumerate the index
space or assume an intermediate execution/output.

The raw list contains the two SHA digests of the issuance proof bytes. These
bytes are explicitly extracted from the represented input, including absent
issuance, reissuance and explicit-amount cases; no extra primitive is added.

Fresh compilation and complete declaration/assumption reporting passed:

```sh
python3 -B proof-work/elements-issuance-proofs/check.py /private/tmp/jet-elements-issuance-proofs.OurYz6Pe
```

`RUN.json` binds11 results and seven definitions: five closed results, five
pure results using inherited functional extensionality and one original C
endpoint with exactly six inherited assumptions. The private source digest is
`33ffafe0efa1a2773f95474fc1a7800c426d878f9346abbb32d57ba8a2c58a51`.
Its explicit separated cache/frame relation places the computed raw hash at
transaction offset536 in the760-byte transaction structure, checked against
the generated layout by the proof.

Recursive kernel/AST verification and canonical-source/evidence review remain.
Actual caller cache construction, formal host-library verification, normal
registration and full acceptance are not claimed. This proof is not part of
the separate447 candidate or its full audit.
