# Original Elements outpoint_hash middle execution

`Middle.op_middle_exec` derives the complete original C pegin/outpoint processing
sequence from represented input, writable private locals and a live SHA context.
Both optional-pegin variants and all Word256 hash/Word32 index values are covered.
The private source advances by 545 bits; the SHA state absorbs 37 or 69 bytes.
The theorem derives exact temporaries, cursor, machine counter, sticky overflow
flag and memory effects, not assumed helper executions or desired results.

This is not yet the full `outpoint_hash` C-to-canonical-specification theorem.
The literal full-program bridge and the public context-read/write/free lifecycle
remain unfinished. The existing `memcpy_model`, initial context representation,
frame/scratch access and private-block separation remain explicit internal
composition premises. The future public proof must discharge the intermediate
premises from its original frame contract and actual local allocations.

## Correct original C order

`Pegin.op_pegin_exec` proves both branches. With no pegin it reads the false
tag, absorbs byte 0, then skips all 256 unused bits. With a pegin it reads the
true tag and 32 payload bytes, absorbs byte 1, preserves the already-read array
through that call, then absorbs those same 32 bytes. This is the actual C order,
not a hoisted prefix write. Both variants consume 257 bits. Padding values are
not constrained to zero.

The final hash/index field is read and absorbed as the original 36-byte C
sequence, using the unchanged `OutpointExec` bounded-call proofs and its actual
36-byte scratch-array type. `Common.op_outpoint_encoding` connects the byte list
to the complete encoded hash/index pair. No field-element or numeric input
restriction is added.

The normal-sequence inverse is reused by a renamed proof from the existing
amount packet; the memory-effect, tag-read, byte absorption, array-preservation,
padding-skip and payload-call lemmas are reused from existing checked/compiled
parents. `Middle.op_middle_then` inserts the verified middle into the exact
right-associated original body with a subsequent writer. Its execution premises
are internal sequencing interfaces, not public equivalence preconditions.

## Verification

```sh
python3 -B proof-work/elements-outpoint-middle/verify.py compile EXTERNAL_DIRECTORY
python3 -B proof-work/elements-outpoint-middle/verify.py kernel EXTERNAL_DIRECTORY
```

Place `Common.v.source`, `Pegin.v.source`, `Middle.v.source` in a fresh external
directory as `.v` files. The driver freshly compiles all three, reports full
types/definitions/assumptions, checks exactly eleven results (seven closed,
four with the existing six inherited CompCert/VST dependencies) and nine
definitions, binds 251 local imports to their forced source/object provenance,
and checks eleven inherited external modules.

`RUN.json` records compilation; `KERNEL-RUN.json` records only a launch. Only
`CHECKED.json` with kernel exit status zero confirms completed recursive kernel
checking for the exact bound inputs. This independent recursive audit checks its
call-foundation dependencies even if the separate parent audit is still running.
Do not edit bound sources, objects or drivers during a live audit.

Unregistered proof work, zero accepted coverage added. Production C, original
specifications, API, generation settings and shared registries are unchanged.

## Continue to the full jet

Port the literal Elements `outpointHash` program: annexHash over the optional
pegin, then ctx8Add32 over the hash and ctx8Add4 over the index. Reuse the existing
literal annex/outpoint option proofs and list-append semantics; preserve the
canonical domain `(Ctx8, (S Word256, (Word256, Word32)))` and both assertion
failure cases. Connect that stream to `op_full_bytes` without changing the
canonical definition or excluding inputs.

Adapt the complete nonce/asset four-local lifecycle to the checked
`OutpointExec.Shape.op_entry`/`op_body`. Keep the real 16/32/36/88-byte allocations,
36-byte scratch permission/free bounds, `op_env` and `_t'3` result. The SHA
reader consumes the first 830 bits; this middle consumes the remaining 545,
making the complete input 1375 bits. The source-copy derivation must use the
36-byte-array environment, not silently identify it with the old nonce one.

Normalize the middle's counter/overflow composition to total lengths 37 or 69,
using the existing sticky-overflow composition lemma, including maximum-counter
crossings. Use `op_middle_then` for the exact writer placement. Reuse the real
initial-memory/frame construction only after the full public C-to-specification
call theorem compiles.
