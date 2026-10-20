# Original Elements outpoint_hash call foundation

This is a checked-by-compilation C call-level foundation, not yet a complete
`outpoint_hash` C-to-Simplicity theorem. The optional-pegin branch, full canonical
program bridge and public context/read/write/free lifecycle remain unfinished.

`Shape.op_body` checks the actual original function body. Unlike the preceding
asset/amount jet, this function has a 36-byte local scratch array. Its input is
1375 bits: a context, an optional pegin hash, and a hash/index outpoint. Its
actual result/tag/context temporaries are `_t'3`, `_t'2`, `_t'1`. `op_entry`
derives the 16/32/36/88-byte allocations; `op_blocks` checks the free-list order
`[ctx:88, src:16, midstate:32, buf:36]`.

## Actual C calls proved

- `Read.op_read_exec` derives the real `read8s` call and byte array/cursor/memory
  effects from encoded input cells and writable scratch. The byte count is
  parameterized from 0 to 36, supporting both actual counts 32 and 36.
- `Read.op_count_cast` proves the actual signed-int-to-unsigned-long conversion
  over those bounded counts; it does not compute an open memory goal.
- `Absorb.op_absorb_exec` derives the actual `sha256_uchars` call, updated context,
  counter, sticky overflow flag and effects, with the existing explicit
  `memcpy_model` premise. `op_array_preserved` transports scratch values across
  unrelated memory changes.
- `Payload.op_payload_exec` composes adjacent read/absorb calls from initial
  representations, using the same count parameter and the original 36-byte
  array type. It is suitable for the final 36-byte outpoint field.
- `FrameOps.op_read_cell` derives the actual tag read and preserves the unread
  encoded cells/context. `op_skip_exec` executes the real 256-bit padding skip.

No desired execution or result is a premise of these call-derivation theorems.
Frame/context/scratch and private-block separation premises remain internal
obligations for the future complete jet theorem. The byte-count bound concerns
an internal C call argument, not a new restriction on logical jet inputs.

## Verification

Copy the five `.v.source` archives to a fresh external directory as `Shape.v`,
`Read.v`, `Absorb.v`, `Payload.v`, `FrameOps.v`. The driver freshly compiles all
five, reports types/definitions/assumptions, checks exactly eleven results and
eight definitions, binds 251 local imports to their forced source/object
provenance, and verifies six inherited external modules. Five results are
closed; the array-preservation fact uses four inherited dependencies; the five
C call theorems use the existing six CompCert/VST dependencies. No new axiom or
unsafe kernel feature is introduced.

This is unregistered proof work with zero accepted coverage added. Production
code, original specifications, API and generation settings are unchanged.

## Continue with the real branch order

The present-pegin branch is **read 32 bytes, absorb byte 1, absorb those 32
bytes**. Do not use the adjacent read/absorb composite across the prefix-byte
call: use `op_read_exec`, the existing generic `nonce_add_byte` in `op_env`,
`op_array_preserved`, then `op_absorb_exec`. Preserve source fields and scratch
values through the prefix call using the existing memory-effect lemmas.

The absent branch reads its false tag, absorbs byte 0, then skips all 256 unused
bits. Padding values need not be zero. Both branches consume 257 bits. Then use
the adjacent payload composite for the 36 bytes encoding hash plus index; the
whole middle consumes 545 bits and absorbs 37 or 69 bytes.

Reuse the existing literal annex/outpoint programs and list-append semantics to
connect the 36-byte C stream to canonical `ctx8Add32` followed by `ctx8Add4`.
The Elements program first applies annexHash to the optional pegin. Retain the
canonical domain `(Ctx8, (S Word256, (Word256, Word32)))` and all count failures.

For the final lifecycle, adapt the checked nonce/asset lifecycle but keep the
actual 36-byte local permission and free bounds. The source-copy proof must be
instantiated for `op_env`; the old nonce environment contains a 32-byte array
and is not definitionally the same. Existing frame-field/initialization helpers
are generic over the other local bindings. Reuse sticky-overflow composition
without assuming an intermediate counter stays below its maximum.
