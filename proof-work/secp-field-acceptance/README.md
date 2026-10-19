# Field multiplication: full registration/acceptance attempt

The checked ordinary-module parent is `../secp-field-integration`. This packet
creates a distinct candidate at `/private/tmp/jet-field-acceptance-5fttrowx`,
retaining its 349 existing registrations and adding only `simplicity_fe_multiply`.
The resulting **350 candidate entries are not an accepted coverage claim**.
The larger pending registry in the main checkout is not replaced or committed.

`prepare.py` adds the exact full-domain public contract, 413 already checked
result audit entries and 299 contract-definition entries. Its coverage guard
rejects the wrong public function, domain, output width, numeric replacement,
weaker contract, added premise, trivial result and a helper offered as the final
jet proof. The normal static gate also runs the checked literal/recursive port
reviews and the FeMultiply catalog/term/full-contract mutation suite.

`run.py generate` runs the complete normal `check-jets.sh --update-expected`
workflow, not a reduced successful substitute. Snapshot generation is separate
from review and a later `run.py accept` (`--accept`, no update/no-build flags).
Long jobs own a dedicated process group and a real bounded deadline. Launch
records are not successful verification; inspect their specific returned live
handle or terminal process record.

## Actual result: blocked before the build by an inherited identity mismatch

The first normal generation attempt **failed**, exit 1, during static checks:

```text
Bitcoin base primitive name mismatch: LockTime
```

`GENERATE-PROCESS.json` records terminal failure. No successful generation,
snapshot review or acceptance receipt exists. The full build, full-registry
kernel/assumption/contract gates and AST regeneration were not reached in this
attempt. Prior focused source-built/kernel evidence for FeMultiply remains
valid, but it is not full repository acceptance.

The new coverage and literal source checks passed, including the ten new
contract mutations plus the helper-registration fixture, before this unrelated
gate failure. The original sources/specifications/APIs, historical checked tree
and main staged patch were not changed. Do not bypass the failing identity
gate or rename the frozen primitive to obtain a passing receipt.

## Reproduction and scope of the finding

From the candidate's `Coq` directory:

```sh
python3 -B check-bitcoin-primitive-identity.py
```

The starting revision `91d89bac` and the current frozen base Coq model both
contain `LockTime => "locktime"` in `Simplicity/Primitive/Bitcoin.v`. The
canonical source `Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs` contains
`primName LockTime = "lockTime"`. These distinct names are inputs to primitive
commitment-tag construction; this is not merely a displayed label. The gate
compares primitive identities, not C execution results. Its failure does not
demonstrate a wrong C lock-time value, a normal-evaluator execution bug, or any
failure of field multiplication. No hash collision claim or unequal digest
proof is inferred from spelling alone.

Identity-dependent Bitcoin correspondence remains unresolved under this gate.
Any target correction requires separate user approval. Continue independent
proof work; the checked field-multiplication loaded closure contains no Bitcoin
primitive module. Preserve this failed attempt rather than rewriting it as a
successful or narrowed acceptance run.
