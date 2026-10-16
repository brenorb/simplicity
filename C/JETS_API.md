# C jet frame contract

This contract applies to individual core, Bitcoin and Elements jet calls. It
supplements the valid-frame and environment preconditions in [jets.h](jets.h)
and the frame representation described in [frame.h](frame.h).

## Input and output buffers must not overlap

The source read frame's backing `UWORD` slice must be disjoint from the
destination write frame's backing `UWORD` slice for the duration of the call.
This is a storage-level requirement, including the words containing frame
padding, not merely a requirement that the logical input and output bits
have different positions.

Separate allocations are not required: disjoint slices of the same allocation
are allowed. For frames constructed with `initReadFrame` and `initWriteFrame`,
the slices are the `ROUND_UWORD(n)` words supplied to those constructors.
All other frame-validity and environment preconditions still apply.

Passing `src` by value copies its frame descriptor, not its backing cells.
A jet may interleave reading input cells with writing output cells; it is not
required to read or copy the entire input before its first output write.
The frame writers may also overwrite cells in front of the destination's
final cursor as documented in `frame.h`.

Overlapping buffers are outside the jet API contract. A jet is not required
to detect such a call, return `false`, or provide `memmove`-style overlap
semantics. Some individual implementations may happen to work with particular
overlaps; that does not extend the API guarantee. This is not a claim that
every overlapping call has undefined C behavior.

## Evaluator and proof boundary

The evaluator in [eval.c](eval.c) maintains disjoint read and write storage in
its gap buffer. Before jet dispatch it checks the corresponding active-frame
edge ordering in debug builds. Stand-alone callers must maintain the same
separation themselves; assertions are not a substitute for that precondition.

The Coq Bit Machine compatibility contracts express storage separation
explicitly through `bm_separated` in
[jet_bitmachine_rep.v](../Coq/C/jet_bitmachine_rep.v). Individual value lemmas
may establish additional cases, but are not a promise that the public API
supports overlapping buffers. No Simplicity jet specification is changed by
this memory-layout requirement.
