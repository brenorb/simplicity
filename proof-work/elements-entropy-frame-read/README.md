# Original entropy jet: entry and input prefix

These five modules prove the actual five-local function entry and all input
reads of `simplicity_calculate_issuance_entropy` in the original Elements AST.
The logical product input is `((Word256, Word32), Word256)`: 544 bits, not 576.
The index is read as exactly the represented Word32, stored in the real
eight-byte `outpoint.ix` field, and preserved through the contract read.

`entropy_read_prefix` derives the five allocations, frame copy, first
`read32s`, `simplicity_read32`, index store and second `read32s` from the initial
encoded input. It accepts arbitrary valid cursors (including crossings),
retains canonical txid/index/contract representations, preserves all old
memory loads and permissions, and retains the fresh locals' ownership for
subsequent calls and cleanup. The local environment's free order is checked
against `blocks_of_env`; it differs from allocation order.

This is preparation for a jet equivalence, not a complete jet theorem. The
existing entropy helper-to-canonical-program theorem still needs composing
with these reads, result copying, output writing, return and all local frees.
No C, specification, API, generation setting or normal registry is changed;
accepted coverage added is zero.
