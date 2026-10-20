# Literal issuance asset-amount getters

Two whole-C contracts are compiled and recursively kernel-checked in
`C.jet_elements_issuance_amount_literal`:

- `elements_issuance_asset_amount_literal_local_spec`.
- `elements_current_issuance_asset_amount_literal_local_spec`.

The literal interpretation follows the canonical `IssuanceAssetAmount`
primitive: Word32 decoding and list indexing, an absent-issuance tag, then
either the new-issuance amount or reissuance amount, with proof data cleared.
The current getter is `CurrentIndex >>> assert IssuanceAssetAmount`. Both reuse
the verified Word64 confidential encoder, generic indexed-value lemma and
current-input transport. This is not the asset/amount pair returned by the
ordinary input/output amount jets, and it is not the token-amount primitive.

The existing original-C execution theorems are composed with these literal
bridges, retaining the exact indexed/current pointer relations, issuance tag
and amount representation, byte offsets, arbitrary writable frame contents,
cursor positions and memory framing. No execution, output, success or extra
libc premise is added. The inherited array/pointer domain and represented
caller environment remain preconditions; construction from arbitrary real
caller memory is not claimed.

## Checked evidence

The every-jet goal remains unfinished. Host-library/cryptographic fidelity,
caller/domain and build-configuration boundaries are not discharged by this
local proof. These receipts describe the actual preserved dirty/staged base,
not a reproducible clean-HEAD build.
