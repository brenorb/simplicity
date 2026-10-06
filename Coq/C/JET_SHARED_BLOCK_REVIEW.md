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

## Byte writer: both generated paths checked

`review_frame_ranges_byte.v` adds five further completed correction-support
results. Two store/load preservation lemmas use the actual byte intervals,
crossing access is extracted from initial capacity, the noncrossing raw writer
is generalized, and `eval_write8_ranges_total` derives the complete original
`simplicity_write8` execution from initial range-separated frame permissions.
The existing raw crossing proof is reused with all intermediate load/store
premises discharged. The actual LSBclear/LSBkeep helpers and generated body
are unchanged. No byte value or backing-word value is restricted.

All original conclusions of `eval_write8_layout` are byte-identical in the
new total theorem: canonical decoded byte, prefix, frame cursor, unchanged
loads outside the cursor/data ranges, permissions and valid blocks. Both
branches construct their stores from initial permissions. The crossing branch
derives preservation of both data words and the two cursor updates from each
word's separation from frame metadata; it assumes no execution or output.

Complete compilation: `/tmp/jet-frame-ranges-byte-compile.log`, session 85401
terminal exit 0. Separate kernel check:
`/tmp/jet-frame-ranges-byte-kernel.log`, session 5977 terminal exit 0, no unsafe
kernel modes; the total theorem retains the same six inherited assumptions.
The receipt `/tmp/jet-frame-ranges-source-review.json` now records this source,
its fresh compiled artifact and additional unchanged dependency hashes.
Exact `Show`/qualified-import and pointer-chunk preservation diagnostics are
in `/tmp/jet-frame-ranges-byte-debug.log` and
`/tmp/jet-frame-ranges-byte-preserve-debug.log`. No statement was weakened.

There are now 12 completed results in these four support modules, separate
from the earlier two-result diagnostic. None is registered as a new jet or
integrated as a public-contract repair. The shared public predicate has 200
direct `.v` consumers; sequence/prefix preservation, reader transports and
actual jet boundaries still require adaptation and substantive review.

## Canonical byte sequences and the actual array loop checked

Eight further completed results in three isolated modules extend this same
correction support:

| Module | Results | Checked boundary |
| --- | --- | --- |
| `review_frame_ranges_sequence` | 4 | Remaining frame after an arbitrary 1–64-bit slice, chained prefix preservation and preservation of already written bits/cells using their actual word intervals |
| `review_frame_ranges_bytes` | 1 | Arbitrary list of actual write8 calls, complete canonical cell output and framing |
| `review_frame_ranges_write8s` | 3 | Initial-array derivation of the run, actual generated write8s function call, and exact encoding of an arbitrary canonical Word8 array |

The sequence theorem retains every original conclusion of
`write8_sequence_run_layout` byte-for-byte. It derives separation for previously
written cells from the initial frame's full capacity, rather than assuming
preservation of those cells. Defined bits and undefined padding cells retain
the original `cell_matches` meaning. Empty lists, arbitrary initial backing
words and all valid cursor crossings remain included.

The array-loop results retain every original conclusion of `write8s_run_layout`,
`eval_write8s_layout` and `eval_write8s_words_layout` byte-for-byte. They derive
each actual unsigned-byte array load and writer call, then instantiate the
existing proof of the generated pointer/count loop, function entry and return.
Neither actual execution nor the internal run witness is a premise of the
total array-writer theorem. Canonical arrays conclude
`concat (map (@encode (Word 3)) xs)`, using the existing universal byte decoding
bridge; no replacement output model is introduced.

The two old input-array block-separation premises (`bi <> bf`, `bi <> bw`)
remain explicit in these array results. This round generalizes frame/data
separation only. It does not certify the admissibility of every remaining
input-array placement or exclusive-end bound.

Complete compilation: `/tmp/jet-frame-ranges-sequence-compile.log` (session
42892), `/tmp/jet-frame-ranges-bytes-compile.log` (26170), and
`/tmp/jet-frame-ranges-write8s-compile.log` (1186), all terminal exit 0.
Independent kernel checks: `/tmp/jet-frame-ranges-sequence-kernel.log`
(32837) and `/tmp/jet-frame-ranges-write8s-kernel.log` (53589), both terminal
exit 0 with no unsafe modes. Execution results retain the six inherited
assumptions; pure preservation results retain four. No new execution, output
or libc premise was added.

The source receipt `/tmp/jet-frame-ranges-source-review.json` now records 20
completed support results in seven modules, fresh compiled hashes and unchanged
dependencies. Exact goal diagnostics for the closed `2^3` bound, local naming
and explicit head-capacity argument are in
`/tmp/jet-frame-ranges-bytes-debug.log`,
`/tmp/jet-frame-ranges-bytes-name-debug.log`,
`/tmp/jet-frame-ranges-bytes-head-debug.log` and
`/tmp/jet-frame-ranges-write8s-debug.log`. Their fixes changed no statement.

Public-contract adaptation is now being prepared in the separate attached
worktree `/Users/brenorb/.codex/worktrees/frame-range-contract/simplicity`,
branch `codex/frame-range-contract`. Its actual `write_frame_at` predicate and
bit/byte writers have a complete scoped rebuild. All dependent callers,
definition/type/assumption review and independent full acceptance are still
required before integration or publication of that candidate. The endpoint
audit remains separate and its inputs are untouched.

These are correction-support results, with zero new jet registrations. The
public repair and exhaustive inherited fidelity review remain incomplete.
