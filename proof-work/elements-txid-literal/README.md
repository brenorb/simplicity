# Elements transaction_id: checked proof and selected source review

Private tree: `/private/tmp/jet-elements-txid.d7yt0o01`.
Fingerprint:
`5e917d5abbccff38685dcce958c687261df5a923f689487022feb7b9369f36b2`.
The source is archived in `source/jet_elements_transaction_id_literal.v.source`.
Only this new source is added to the exact completed token-bundle tree. Main,
all inherited sources and the original staged patch remain unchanged.

`elements_transaction_id_literal_local_spec` reuses the existing whole-C
transaction_id execution proof and the checked four-limb digest decoder. It
retains `hash_getter_rep ... 0 664 760`, requiring that the cached C transaction
identifier represents the logical transaction's `txid`. No new execution,
output or framing premise was introduced. This does not prove that the C
environment constructor computes that cached identifier.

Checker57611 terminated with exit0: the inherited execution module and new
bridge compiled freshly, both results and the definition were printed in full,
the generated Elements AST check passed, and recursive `coqchk` passed. The
pointwise conversion uses inherited functional extensionality; the C endpoint
has exactly the six inherited Coq/CompCert assumptions. Neither is claimed
axiom-free. `RUN.json`, `CHECKED.json` and archived logs bind these facts;
`review.py PRIVATE_TREE` independently verifies the proof and source checkpoint.

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

Independent finish30226 terminated with exit0:63 selected source corruptions
and36 proof/evidence/object/kernel-scope corruptions were rejected. The source
fixtures are confined to the selected serializer where expressions have
unrelated textual look-alikes. `EVIDENCE-REVIEW.json` binds the five tools,
completed proof receipts and all three terminal source/evidence commands/logs.
No Coq proof or accepted source changed during this review.

## Remaining work before any coverage claim

Normal delta preparation is tracked in `../elements-txid-admission/` over the
reviewed417 candidate. Preserve all inherited records and dependencies, run
full acceptance and guarded source-only integration. No normal registration,
coverage increment, full acceptance, caller cache construction or formal host
library equivalence is claimed by this folder. The every-jet goal remains active.
