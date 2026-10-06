# Shared frame/data blocks: validated contract-domain exclusion

Status: **restriction validated; public-contract repair remains open**.
This is inherited memory-contract review. It adds no jet coverage and changes
no production C, generated AST or canonical program.

## Concrete case and actual C execution

The shared contracts `write_frame` (`jet_frame_spec.v:29–37`) and
`write_frame_at` (`jet_output_layout.v:9–20`) require `bf <> bw`: the frame
structure and its UWORD data must occupy different CompCert blocks. This is
stronger than non-overlap of the actual byte intervals read/written.

A completed proof constructs a single 24-byte allocation with this layout:

| Byte interval | Initial value | Final value after actual writeBit(true) |
| --- | --- | --- |
| [0,8) | frame.edge = pointer to offset 16 in the same block | unchanged |
| [8,16) | frame.offset = 64 | 63 |
| [16,24) | UWORD data = 0 | 0x8000000000000000 |

The intervals are eight-byte aligned and mutually disjoint. This represents
the ordinary layout of a frameItem followed by one UWORD in an enclosing
structure under the pinned ABI (frameItem is 16 bytes, UWORD is eight bytes).
For example, the C geometry is:

```c
struct { frameItem frame; UWORD data[1]; } storage;
storage.data[0] = 0;
storage.frame.edge = storage.data;
storage.frame.offset = UWORD_BIT;
writeBit(&storage.frame, true);
```

This snippet illustrates the layout; the verification evidence is the actual
Clight call below, not a native build with a different host UWORD width.
The original `C/frame.h:80–90` decrements the cursor, loads the edge, computes
the data pointer and updates the selected bit. No separate-block condition
appears in that body or its documented valid-write-frame precondition.

`embedded_frame_writeBit_exists` constructs initial memory using Mem.alloc
and three successful stores. It derives writable cursor/data permissions and
the two stores performed by the writer. Its conclusions include:

- actual `Clight2.eval_funcall ge0` of `Internal f_writeBit`, E0, true return;
- exact final edge/cursor representation and UWORD value shown in the table;
- rejection by the existing `write_frame_at` for even one output cell.

Execution, output and final memory are conclusions. They are not hypotheses
of the witness theorem. No output premise, impossible initial assumption or
modified C body makes the example succeed. The initial block is only 24 bytes;
this case has none of the extreme-allocation reachability question in the
separate endpoint diagnostic.

## Reusable repair evidence and limits

The diagnostic's `eval_writeBit_layout_ranges` proves the same actual writer
for arbitrary initial memory/addresses under:

```
bf <> bw \/ word_address + 8 <= base \/ base + 16 <= word_address
```

Its premises otherwise preserve the original layout/helper contract. It follows
the real generated body and derives load preservation through byte-interval
separation. It handles both boolean branches, including the actual linked
LSBclear on false. The concrete witness derives its store premises from initial
writable permissions and instantiates the same-block third alternative.

This supplies a checked proof pattern for replacing a blanket block-identity
restriction with actual memory separation. It does not yet generalize every
writer, reader, wrapper, memcpy caller or whole public jet contract. Overlapping
frame metadata and output words must still be excluded where needed; removing
all separation would not be a valid repair.

Existing registered results remain theorems under their stated predicates.
This is a confirmed domain exclusion in shared predicates, not a wrong C output
or a newly proved whole jet. The complete inherited review cannot be certified
while the exclusion's public scope is unresolved. Legitimate numeric domains,
canonical specifications and final output/framing conclusions must be preserved
when widening the memory domain.

## Verification evidence

The complete isolated source is
`/Users/brenorb/.codex/jet-proof-scratch/original-c/review_frame_same_block.v`.
It contains two completed results: the generic range-separated writer proof
and the constructed execution/domain-exclusion witness.

- Complete compilation: `/tmp/jet-frame-same-block-review-compile.log`, exit 0
  (session 31427 terminal).
- Independent kernel check: `/tmp/jet-frame-same-block-review-kernel.log`, exit 0
  (session 51517 terminal), with no unsafe kernel options.
- Both results retain the same six inherited classical/extensionality/CompCert
  assumptions; no added helper execution, output or libc premise.

The first proof attempt needed an explicit normalization of the cursor field's
offset `0+8` before a store-preservation rewrite. The exact goal was inspected
with Show; the statement was unchanged.

## Remaining obligations

1. Replace or justify the separate-block requirements at actual public
   boundaries; an undocumented allocation convention is insufficient.
2. Generalize helper preservation, sequencing and caller contracts using
   appropriate byte footprints, including both noncrossing/crossing writes.
3. Recheck all affected full conclusions and legitimate initial domains, then
   review types/definitions/assumptions and perform independent final acceptance.
4. Keep the registered inventory (347/533; 104 libc-conditional) distinct from
   exhaustive fidelity certification. No new registration is made here.
