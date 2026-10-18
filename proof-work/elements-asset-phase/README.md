# Original Elements asset prefix and payload execution

This is a partial C execution proof toward `simplicity_asset_amount_hash`,
not a complete jet-equivalence theorem. The amount phase, context lifecycle,
canonical-program bridge and final public composition remain unfinished.

`Asset.asset_phase_exec` executes the original asset prefix and 32-byte payload
operations from readable input, writable private scratch and a live SHA context.
It covers explicit assets and both confidential parities, using the real prefix
bytes 1, 10 and 11. It derives the updated context, counter, sticky overflow
flag, 258-bit private cursor advance and memory effects. No helper execution or
desired output is a premise. The existing external `memcpy_model` is explicit.
Private-block separation and the initial context representation remain internal
composition premises to be discharged by the future whole-call proof.

## Reusable structure and original AST

`Prefix.tagged_explicit_prefix` and `Prefix.tagged_confidential_prefix` factor
the checked nonce prefix derivations over temporary identifiers and confidential
prefix-byte constants. The latter takes explicit pure byte-representation
equalities, discharged by the closed `asset_prefix_machine` result for 10/11.
The explicit prefix remains 1. Both retain arbitrary Word256 payloads, including
the real padding-bit skip in the explicit branch. The checked nonce payload
reader/absorber and memory-effect lemmas are reused without modifying them.

`Shape.asset_amount_body` proves equality with the actual original Clight body.
The input is 1346 bits (context 830, asset 258, amount 258). The body retains
the original right-associated statement order, actual six temporary variables,
eight-byte explicit amount read, `257 - 64` padding skip, 32-byte confidential
amount read, and `_t'6` result. `asset_amount_entry` derives all four local
allocations. The grouped asset phase needs ordinary statement-sequence
composition when inserted into that full body; no equality with the nonce jet
or with the entire asset/amount function is asserted.

The nine fresh results have exactly five closed proofs and four with the six
inherited CompCert/VST dependencies. The twelve definitions and full result
types are recorded in the reports. No new axiom, production implementation,
original specification, API change or generation-setting change is introduced.
No canonical option equivalence is claimed by this packet.

```sh
python3 -B proof-work/elements-asset-phase/verify.py compile EXTERNAL_DIRECTORY
python3 -B proof-work/elements-asset-phase/verify.py kernel EXTERNAL_DIRECTORY
```

Place the three `.v.source` archives in a fresh external directory as `Prefix.v`,
`Shape.v`, `Asset.v`. The driver freshly compiles them, checks the exact
result/definition/assumption profile, binds 251 local imports to their forced
source/object provenance, and verifies the seven inherited external modules.
It requires the completed nonce-phase kernel receipt.

`RUN.json` records compilation only; `KERNEL-RUN.json` records a launch only.
Only `CHECKED.json` with kernel exit status zero establishes completed recursive
kernel checking for its exact bound inputs. The initial pre-checkpoint compile
record and driver are preserved privately as `first-RUN.json` and
`first-verify.py.source`; a driver docstring was clarified to say phase rather
than whole jet, followed by a fresh complete compile/report run. The Coq proofs
were unchanged by that clarification.

This work is unregistered. Accepted coverage added is zero; the broad all-jets
goal remains unfinished.
