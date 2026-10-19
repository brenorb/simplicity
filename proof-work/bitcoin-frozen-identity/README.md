# Frozen Bitcoin LockTime identity mismatch: checked negative diagnostic

The complete normal registration gate for `fe_multiply` stopped at an inherited
Bitcoin identity mismatch before reaching its build. This packet formally
confirms the mismatch without changing the target or weakening the gate.

`Frozen.v.source` contains three **closed**, freshly compiled and recursively
kernel-checked theorems:

1. The unchanged base model's `Bitcoin.name Bitcoin.LockTime` is `"locktime"`.
2. That name is not `"lockTime"`, the name in the canonical Haskell source.
3. The actual frozen `Bitcoin.tag Bitcoin.LockTime` is unequal to the Coq tag
   construction with prefix `Bitcoin` and canonical-name input `"lockTime"`.

The third result is an exact closed computation in Coq, not an appeal to hash
collision resistance or an inference from spelling. It observes the first
register of the two concrete tags and proves their inequality. The relevant
base Bitcoin, Primitive and MerkleRoot source files are checked byte-for-byte
against starting revision `91d89bac`. No name, semantic function, domain,
primitive identity, C implementation or API was corrected.

## Is this a C jet bug?

This is a demonstrated mismatch between the frozen base Coq identity and the
canonical-name tag construction. The canonical Haskell primitive declaration
and name are at `Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs`. The existing
identity gate detects it independently:

```sh
cd Coq
python3 -B check-bitcoin-primitive-identity.py
# Bitcoin base primitive name mismatch: LockTime
```

It is **not** a demonstrated C lock-time-value error, evaluator bug, fund-loss
scenario, or `fe_multiply` failure. The computation here is entirely formal
Coq computation, not a native C execution test. It does not prove a general
Coq-to-Haskell hashing translation, or classify which artifact should change.
Any correction requires separate user approval under the frozen-target goal.

The potential impact is incompatible primitive commitments when a consumer
treats the base-model LockTime tag as canonical. We have not established an
exploit, consensus acceptance/rejection scenario, or propagation of this
inequality through every enclosing hash construction. Identity-dependent
Bitcoin acceptance remains unresolved; independent core proofs may continue.

## Evidence and reproduction

The isolated source is
`/private/tmp/jet-field-acceptance-5fttrowx/identity-diagnostic/Frozen.v`, under
the narrow `FrozenBitcoin` namespace. `RUN.json` binds the exact source,
object, freshly compiled commands/reports and loaded project dependencies;
`CHECKED.json` binds the successful recursive kernel check. All three theorem
assumption sets are empty, and no new library axiom or unsafe-check category
is allowed. Full types, assumptions, loaded-library inventory and kernel
output are archived alongside the receipts.

```sh
python3 -B proof-work/bitcoin-frozen-identity/check.py
```

`verify.py compile` and `verify.py kernel` are one-shot audit phases already
completed for this exact tree. Do not overwrite their historical receipts or
rerun a live job on an observation timeout. The full normal build running in
the separate acceptance candidate does not load or modify this diagnostic
extension; it cannot turn the failed identity gate into acceptance.
