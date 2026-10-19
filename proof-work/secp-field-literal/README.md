# Original C `fe_multiply` against its literal Simplicity specification

The completed candidate theorem is
`FieldLiteral.Jet.fe_multiply_literal_local_spec` in `Jet.v.source`:

```coq
secp_jet_local_spec f_simplicity_fe_multiply
  (Ty.Prod (Word 8) (Word 8)) (Word 8)
  (@literal_fe_multiply Alg.CoreFunSem).
```

This proves the actual original public C function's execution and successful
Boolean return, exact specification output encoding, preserved output prefix,
correct output-frame cursor, and permitted-memory-change/load contract. It
uses the existing complete public contract, not a weaker output-only theorem.
Both Word256 inputs are unrestricted, including values at or above the prime.
No helper execution, intermediate representation, limb bound, final memory
fact, external-library model or result is an added premise.

The actual entry, three allocations, by-value source-frame copy, two readers,
in-place field multiplication, original normalization/serialization writer,
return conversion and all three frees are discharged by the checked public
parent and its source-built dependency chain. The proof is for the unchanged
LP64 Clight program and generation configuration; other builds are not claimed.

## The specification is not replaced by arithmetic

The final theorem reuses the existing `literal_fe_multiply` from
`C.jet_secp_negate_literal_contract`: literal multiply at Word256 followed
by literal modulo at Word512 and low-half projection. The recursive division
port retains its canonical-add calls. `Spec.v.source` proves that the already
established numeric C result equals this term's result. The numeric bridge
is not registered or presented as a substitute specification.

25 additional original proof modules, including the word-conversion
foundation, were freshly rebuilt from sources identical to the checkout.
`DEPENDENCIES.json` binds every source, object, compiler command and log.
The reused pending negation sources were not edited or staged.

`ARCHIVED-INPUTS.json` binds byte-identical copies of all 25 newly loaded
proof sources and the reused gate/reference files under `inherited/` to the
checked receipts. This preserves the required shared inputs on the proof
branch without staging their pre-existing uncommitted originals. Restore
these files only into an isolated candidate at their recorded original
paths, never overwrite the checkout's pending work. These copies provide
the source closure; they do not make the historical receipt match a different
registry/build snapshot. Such integration still needs fresh evidence.

The source-review layer checks the original FeMultiply catalog/type/record
binding, the existing literal term and complete final public statement; it
also reruns the existing recursive-port, literal-add, foundation and
normalization/field-constant/full-contract checks. Their mutation suites
reject **173** targeted changes (19 + 86 + 15 + 32 + 11 + 10). These are
scoped source-correspondence checks supplementing the formal Coq proof,
not a theorem translating arbitrary Haskell. No reference JSON or gate pin
was updated to obtain success.

The gates expect proof sources and their reviewed JSON in one candidate
directory. The isolated view `/private/tmp/jet-multiply-literal-ports.BsO6pV`
contains links to the unchanged checkout proof sources and a byte-identical
copy of `recursive-ports-review.json`. The verifier binds all accessed
candidate files and gate/reference inputs. An earlier preflight pointed at
`Coq/C` alone and failed to locate that JSON; correcting the invocation/view
resolved it without changing a specification, proof or review reference.

## Verification receipt

Two new sources, four results, no new program definitions. The two semantic
bridges inherit only the existing dependent functional-extensionality axiom;
the two public execution/contract endpoints retain the same six inherited
Coq/CompCert dependencies as the checked C parent. No new axiom declaration,
admission, unsafe cast, disabled kernel check or external model is introduced.

The exact loaded provenance covers **176 source-built local modules and 59
extension modules**, including these two. The full type/assumption reports
are `literal-contracts.log` and `literal-assumptions.log`. `RUN.json` binds
fresh compilation, all twelve source-review commands/logs and exact inputs;
`CHECKED.json` additionally binds the completed successful recursive kernel
check. The kernel context must retain the existing allowlist and empty
type-in-type, unsafe-fixpoint and assumed-positivity categories.

```sh
python3 -B proof-work/secp-field-literal/verify.py compile \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-literal/verify.py kernel \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-literal/verify.py check \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
```

These are guarded, separate phases; launch records alone do not prove
completion. Poll a live process instead of restarting it on an observation
timeout. Preserve the frozen checked sources, objects and review inputs.

## Integration remains separate

This is a checked complete individual-jet proof candidate. It is not yet
materialized into the regular proof build or registered/accepted in the
shared coverage inventory. Public accepted-coverage delta remains zero.
Preserve the unrelated staged patch while promoting the source-built helper
chain and final theorem into an isolated acceptance candidate; review all
new contracts/assumptions and rerun the normal acceptance gates before
updating accepted coverage. Do not rewrite historical receipts when their
input inventories differ: preserve them and create new integration evidence.

The overall all-jets goal is still incomplete. Production C, original
specifications and identities, API, generation settings, main proof sources,
shared registries and the unrelated staged patch are unchanged by this work.
