# Literal issuance asset-amount getters

Two whole-C contracts are compiled and recursively kernel-checked in
`C.jet_elements_issuance_amount_literal`:

- `elements_issuance_asset_amount_literal_local_spec`.
- `elements_current_issuance_asset_amount_literal_local_spec`.

Private tree: `/private/tmp/jet-elements-issuance-amount-literal.j6pW3K`.
Input SHA-256:
`9989f6abba080fc2df15fe62d2eeb13a14014038b9a2324c7143f1d624cfe0d3`.
The seed is the completed amount proof tree, not a live normal audit. Its
inherited sources are unchanged; the only new proof source is archived in
`source/jet_elements_issuance_amount_literal.v.source`.

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

Checker82011 terminated with exit0. It freshly compiled the original indexed
C execution module, original current-input C module and new literal module;
printed all five results and three definitions; checked the Elements AST; and
recursively kernel-checked the new module and its dependency closure. Both C
endpoints retain exactly the six inherited Coq/CompCert assumptions. The local
encoder-selection lemma is closed; the two primitive transports retain the
existing functional-extensionality dependency. `CHECKED.json` binds sources,
objects, commands, full reports and terminal logs.

The independent source/evidence finish17795 terminated with exit0. Its guards compare
the Haskell primitive, catalog and current-input program with the Coq port,
literal definitions, original and transported whole-C statements and actual C
helper/wrapper bodies. They reuse the completed amount-family encoder guards.
All47 source corruptions and38 independent evidence/object/kernel-scope
corruptions were rejected. `EVIDENCE-REVIEW.json` binds the completed checker,
source fingerprint, all five tools and all three review commands/logs. Neither
normal registration, full normal acceptance nor main installation has occurred.

The every-jet goal remains unfinished. Host-library/cryptographic fidelity,
caller/domain and build-configuration boundaries are not discharged by this
local proof. These receipts describe the actual preserved dirty/staged base,
not a reproducible clean-HEAD build.
