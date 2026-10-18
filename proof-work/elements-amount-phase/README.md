# Original asset/amount middle execution

`Compose.asset_amount_middle_exec` derives the entire original asset and amount
processing sequence of `simplicity_asset_amount_hash` from represented input,
writable private locals and a live SHA context. It does not assume any desired
helper execution or output. All asset/amount variants are included, with
arbitrary Word256/Word64 payloads and arbitrary valid frame positions.

This is not yet a full C-to-canonical-jet equivalence theorem. Context parsing,
the canonical option-program bridge, final context writing and local freeing
still need to be composed at the public function boundary. No accepted coverage
is added by this unregistered packet.

## Proven C steps

- `Payload8.amount_payload8_exec` reads and absorbs eight bytes for an explicit
  amount, using the original 32-byte scratch-array type and original calls.
- `Common.amount_skip_exec` evaluates the actual C `257 - 64` expression and
  executes the 193-bit padding skip. Encoded padding cells retain their physical
  readability meaning; no value constraint is added to unused bits.
- `Phase.amount_explicit_exec` derives the real tag read, byte-1 absorption,
  padding skip, eight-byte read and absorption.
- `Phase.amount_confidential_exec` derives both confidential parity branches,
  byte 8/9 absorption, and all 32 payload bytes.
- `Phase.amount_phase_exec` combines every amount input. Both branches consume
  258 bits, but absorb different lengths: 9 versus 33 bytes.
- `Compose.asset_amount_middle_exec` composes this with the unchanged asset
  phase (33 absorbed bytes), preserving the original right-associated statement
  order. It derives the 516-bit private cursor advance, exact updated temporaries,
  SHA state, machine counter, sticky overflow flag and memory effects.
- `Seq.amount_seq_normal_inv` and `Compose.asset_amount_middle_then` support
  reinserting the checked phase into the exact actual body with a final writer.
  Execution premises of these sequence lemmas are internal composition interfaces,
  not public correctness premises.

The conditional external premise remains `memcpy_model`. Context representation
and separation of private local/input/global blocks are internal premises; the
future public proof must derive them from its original frame contract and actual
allocations. The middle proof permits an already-set overflow flag and does not
exclude inputs that fail the canonical context-count check.

## Verification

```sh
python3 -B proof-work/elements-amount-phase/verify.py compile EXTERNAL_DIRECTORY
python3 -B proof-work/elements-amount-phase/verify.py kernel EXTERNAL_DIRECTORY
```

Copy the five `.v.source` archives to a fresh external directory as `Common.v`,
`Payload8.v`, `Phase.v`, `Seq.v`, `Compose.v`. The driver freshly compiles them,
reports all types/definitions/assumptions, checks exactly thirteen results
(five closed, eight with the six inherited CompCert/VST dependencies) and eight
definitions, binds 251 local imports to their forced source/object provenance,
and checks ten inherited external modules.

`RUN.json` records compilation, `KERNEL-RUN.json` only a launch; only a successful
`CHECKED.json` records completed recursive kernel checking for the exact bound
inputs. The parent asset-phase audit need not finish before this independent
recursive audit, which checks that dependency itself. Do not edit bound sources,
objects or drivers while their audit is live.

Production C, original specifications, generation settings, API and shared
registries are unchanged. This proves actual C execution against its byte-stream
model; it does not independently claim the remaining literal-program bridge.

## Next full-jet composition

Reuse the complete four-local lifecycle in `elements-nonce-local/Local.v.source`.
The original asset/amount entry and body are already checked in
`elements-asset-phase/Shape.v.source`. Locals are the same 16/32/32/88 bytes,
but the actual function has six temporaries and returns `_t'6`. After the SHA
reader consumes 830 bits, call the middle theorem for the remaining 516 bits;
the complete logical input is 1346 bits. Use `asset_amount_middle_then` to insert
the writer without assuming syntactic associativity of statements.

Reuse the canonical serializer proofs in
`elements-amounts-hash/source/jet_elements_asset_amount_hash_spec.v.source`
and the tagged-word helper, freshly compiling their pure dependencies in a new
external tree rather than changing the frozen SHA basis. Connect the existing
asset/amount byte lists by explicit constructor cases and retain all inputs.

Normalize the four incremental counter/overflow updates to total length 42 or
66 for the context writer. A proof must cover crossing the maximum counter:
do not assume the asset phase leaves the overflow flag false. The existing
context-value bridge then relates the final total to the canonical option
result, including invalid initial counts and overflow failures. Reuse the
already checked real initial-memory/frame construction only after that full
public lifecycle theorem compiles.
