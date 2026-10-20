# Elements issuance_range_proofs_hash: reuse the two-primitive reader loop

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
