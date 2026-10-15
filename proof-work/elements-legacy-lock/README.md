# Legacy Elements relative-lock getters

Two **unregistered** whole original-C equivalence theorems now compile:
`elements_broken_tx_lock_distance_local_spec` and
`elements_broken_tx_lock_duration_local_spec`. They preserve the historical
`broken_do_not_use` behavior; they do not repair consensus behavior or reuse
Bitcoin's different current-input specification.

Private tree: `/private/tmp/jet-elements-legacy-lock.0mJMjD`.
It was APFS-copied from the completed 402 normal candidate, never from a live
audit's objects. All inherited source/metadata are byte-identical. Four new
modules are archived in `source/` and excluded from main's active build.
Main remains 399/533; none of this work changes a registry or existing audit.

## End-to-end statements and boundary

The canonical core/primitive programs retain the Haskell `forWhile word32`
body, including `parseSequence`, `max word16`, the version check, and zero for
versions below two. They fold over every input sequence, not just the current
input. The shared `for_while_run_fold_list` proves finite state-carrying indexed
folds at arbitrary counter depths without enumerating the 2^32 counters.

The C proof derives the real helpers' two branches and a reusable
width-polymorphic helper/write composition. On this LP64 translation unit,
`uint_fast16_t` is a 64-bit carrier; both cached fields are loaded as Mint64
at verified offsets 736/744, with version at 720. The complete jet derives
entry, allocation and by-value source copy, helper execution, write16,
return/free, output/prefix/cursor and outside-memory observations from initial
frames. Arbitrary initial output, valid offsets and crossings are retained.

The environment relation requires the initial cached transaction field to
represent the maximum of the selected low-16-bit sequence payloads, plus the
logical version. This is an explicit cache-representation boundary, not a
proof that env.c establishes that cache. No helper-execution or writable-output
value is assumed. Caller construction/preservation is a separate obligation.

## Verification and next work

All four modules freshly compile with Coq 8.17.1 / OCaml 4.14.4. The checker
printed complete reports for **32 results and 19 definitions**: 21 results are
closed, and both whole-C endpoints retain precisely the six inherited
Coq/CompCert assumptions, without an extra libc premise. Elements AST
regeneration also passed. Source input:
`72b6728a0d20b01799638071bbc39936e4bc71e8ede50d22626db0c77a98239a`.

Recursive kernel checking is live as **42973**; poll that handle rather than
restarting it. `RUN.json` binds the fresh compilation, reports, source/object
hashes, preserved main inputs and original staging. Only `CHECKED.json`
confirms recursive kernel success; a launch receipt is not a terminal result.

```sh
ulimit -s 65520
python3 -B proof-work/elements-legacy-lock/check.py /private/tmp/jet-elements-legacy-lock.0mJMjD
```

Do not repeat a launched checker. Its canonical source/corruption guard is not
yet complete, and there is no normal registration or full normal acceptance.
Before admission, freeze the selected Haskell dispatch, complete loop/core
definitions and conversion interfaces with source/corruption review; inspect
every actual public type/definition/dependency delta. Afterwards extend the
same execution/specification infrastructure to the two assertion/check jets,
and connect the cached aggregate relation to the actual environment builder.

Debugging lessons: pass the logical state Ty explicitly to the generic fold;
distinguish Primitive's projected Core algebra from a printed-identical
Reader Core instance (`change ... in HB` aligns the actual hypothesis);
use named reader composition lemmas and opaque proven core terms instead of
expanding symbolic arithmetic. For destination lookup, exactly two PTree.gso
rewrites suffice; an unbounded rewrite can descend into the generated temps.
