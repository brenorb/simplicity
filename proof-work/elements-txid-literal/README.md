# Elements transaction_id: checked proof and selected source review

`elements_transaction_id_literal_local_spec` reuses the existing whole-C
transaction_id execution proof and the checked four-limb digest decoder. It
retains `hash_getter_rep ... 0 664 760`, requiring that the cached C transaction
identifier represents the logical transaction's `txid`. No new execution,
output or framing premise was introduced. This does not prove that the C
environment constructor computes that cached identifier.

Two initial compiler errors were an absent import for `hash_getter_rep` and a
missing integer scope. They were corrected before the successful fresh check;
no admissions or unchecked casts were used.

## Selected canonical serialization review

The target uses the existing Coq port's `txid`. Its complete selected source
correspondence has now been reviewed, not only `interpret TransactionId`:

- Haskell `specificationTransaction TransactionId`, primitive type/name,
  `encodeHash`, `element` and the logical environment transaction projection.
- `putNoWitnessTx`: version/lock little endian, the zero marker, varint bounds,
  ordered inputs/outputs, issuance/pegin flag bits, outpoint/script/sequence
  serialization, new issuance's zero nonce and reissuance's zero token byte.
- `putAsset`, `putAmount`, `putNonce`, cleared proofs, packed field coordinates,
  and issuance's special explicit-zero encoding; retain the actual domain.
- `txid = bslDoubleHash . runPutLazy . putNoWitnessTx`, the digest byte carrier,
  and the already checked four-limb hash-to-word conversion. Source comparison
  is not a formal host-library equivalence theorem.
- Exact Coq definitions and whole-C contracts, with mutation tests for routing,
  byte order, flags, varints, tags, zero cases, representation and framing.

`check-source.py` checks the complete Haskell no-witness serializer, all18
selected Coq serialization/hash definitions, the packed-field/native-nonce and
four-limb decoder dependencies, represented transaction/script bounds, the
actual C getter body, exact unchanged representation and both whole-C contracts.
Source comparison does not prove a Haskell compiler, host serialization/crypto
library or C environment-constructor theorem. It adds no logical assumptions.

## Remaining work before any coverage claim

Normal delta preparation is tracked in `../elements-txid-admission/` over the
reviewed417 candidate. Preserve all inherited records and dependencies, run
full acceptance and guarded source-only integration. No normal registration,
coverage increment, full acceptance, caller cache construction or formal host
library equivalence is claimed by this folder. The every-jet goal remains active.
