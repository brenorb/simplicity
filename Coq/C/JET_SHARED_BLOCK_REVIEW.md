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

## Total writer and sequencing support checked subsequently

Three isolated modules now add seven completed results for the same correction,
without changing the public predicates, production C, ASTs or canonical programs:

| Module | Completed results | Exact role |
| --- | --- | --- |
| `review_frame_ranges_total` | 3 | Initial range-separated frame predicate, implication from the old predicate, head extraction and total actual writeBit execution |
| `review_frame_ranges_step` | 3 | Capacity restriction, store-based preservation and total writer with a derived remaining-frame contract |
| `review_frame_ranges_embedded` | 1 | Constructed 24-byte initial memory, arbitrary initial UWORD and both Boolean inputs, full writer conclusions and 63 remaining writable cells |

The first module replaces blanket `bf <> bw` with separation of each word
that can be touched from the frame's byte interval `[base,base+16)`. The old
predicate implies this candidate for every old input. The total writer derives
both actual stores from initial Writable permissions and proves the actual
Clight function call; execution, stores, final memory and output are not
preconditions of that total theorem. Its complete original output/framing/
permission conclusion is byte-identical to `eval_writeBit_layout`'s conclusion.

The step module additionally derives a valid range-separated frame at
`cursor-1` with `count-1` cells. Its intermediate store-preservation lemma
takes store facts, but the total theorem constructs and discharges those facts.
Preservation handles both a repeated write within a word and a transition to
another word; the proof derives separation between distinct UWORD addresses
from their eight-byte spacing. No remembered output value is assumed for the
remaining cells. This is sequencing support, not a complete multiwriter or
whole-jet equivalence.

The ordinary shared-block instance establishes the initial predicate for all
64 cells of an arbitrary UWORD, executes the actual writer for either Boolean
value, and derives the exact output bit, prefix preservation, cursor 63,
unchanged loads outside the two modified ranges, preserved permissions/valid
blocks and capacity for the next 63 writes. The existing public predicate still
rejects this instance. Both the public predicate repair and all dependent
reader/writer/caller transports remain outstanding.

The candidate retains the old exclusive-end address bounds; it does not claim
to settle the separately documented endpoint admissibility question. Adding
the remaining-frame conclusion strengthens the support theorem; it does not
weaken any existing output conclusion or alter a canonical specification.

Evidence:

- All three complete sources are in
  `/Users/brenorb/.codex/jet-proof-scratch/original-c/` under the module names
  above. Source/compiled hashes and 15 unchanged dependency/source hashes are
  recorded in `/tmp/jet-frame-ranges-source-review.json`.
- Complete compilation: `/tmp/jet-frame-ranges-total-compile.log` (session
  55846), `/tmp/jet-frame-ranges-step-compile.log` (3711), and
  `/tmp/jet-frame-ranges-embedded-compile.log` (25831), all terminal exit 0.
- Independent kernel check of all three modules:
  `/tmp/jet-frame-ranges-kernel.log`, session 70209 terminal exit 0; no unsafe
  kernel modes. Total execution results retain the six inherited
  classical/extensionality/CompCert assumptions and add no libc, execution or
  output premise.
- The first preservation rewrite needed explicit byte-range cases. Exact
  `Show` evidence is in `/tmp/jet-frame-ranges-total-debug.log`. Two missing
  imports were diagnosed with `Show` and qualified `Check` in
  `/tmp/jet-frame-ranges-step-debug.log` and
  `/tmp/jet-frame-ranges-step-import-debug.log`; statements stayed unchanged.

These results are verified correction support, unpublished as repository proof
modules. They add **zero** registered jets and do not complete the global
inherited review or the public memory-contract repair.
