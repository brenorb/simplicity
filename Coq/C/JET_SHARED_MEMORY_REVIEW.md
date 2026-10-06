# Shared memory-contract review: endpoint boundary

Status: **partial; a semantic-domain restriction is validated and its repair
is under verification**. This is part of inherited fidelity review, not new
jet coverage. It does not change the production C or canonical programs.

## Validated restriction and exact scope

At published proof tree `3fbfa722`, `jet_frame_layout.v:10–11` defines
frame_base_valid as `0 <= base /\ base + 16 <= Ptrofs.max_unsigned`. The bound
compares the exclusive end of a 16-byte frame object with the maximum pointer
offset, rather than with the one-past limit `Ptrofs.max_unsigned + 1`.

An isolated, completed diagnostic constructs a CompCert memory and checks:

| Fact | Checked boundary |
| --- | --- |
| Frame object starts at a representable, eight-byte-aligned offset | base = 18446744073709551600 = 2^64 - 16 |
| Pointer field is readable | Mptr at base, value is an actual Vptr |
| Cursor field is writable and readable | Mint64 at base+8 = 2^64 - 8, value zero |
| Complete frame object can be copied as bytes | Mem.loadbytes at base for 16 bytes succeeds |
| Actual Clight field address is representable without wraparound | unsigned(add(repr(base), repr(8))) = base+8 |
| Actual generated-layout field expression evaluates | Efield/Ederef/Etempvar for frame.offset in ge0 returns Vlong zero |
| Existing frame predicate nevertheless rejects the object | not frame_base_valid base, since base+16 = 2^64 |

The memory is constructed through Mem.alloc and actual successful stores.
Permissions and loads follow from CompCert memory lemmas; execution of the
field expression is a conclusion, not an assumption. No hypothetical failing
jet execution or desired canonical output is supplied as a premise.

**What this proves:** the shared predicate excludes a range and field access
which the chosen CompCert/Clight memory semantics accepts. It disproves the
claim that the current bound follows merely from representability of the
field pointers, accessibility of the object or absence of address wraparound.

**What it does not prove:** a complete jet counterexample, a wrong output or
failure in the C implementation, or reachability of this extreme allocation
through the real x86-64/Linux allocator. The diagnostic allocation has an
exclusive upper bound 2^64. Its relationship to reachable target allocations
is a separate admissibility question. It does not establish that every
other initial-frame/environment predicate accepts all legitimate placements.

Existing theorems remain theorems under their explicit predicates. They must
not be represented as an exhaustive review of all legitimate memory placements
while this shared-contract question remains unresolved. No registered entry
is promoted or removed solely on this diagnostic.

## Verification evidence

The complete file is outside repository build load paths:
`/Users/brenorb/.codex/jet-proof-scratch/original-c/review_frame_endpoint.v`.
Its five closed results include endpoint representability/rejection, a
constructed memory witness and actual Clight offset-field evaluation.

- Compilation: `/tmp/jet-frame-endpoint-review-compile.log`, exit 0
  (session 42901 terminal).
- Independent kernel check: `/tmp/jet-frame-endpoint-review-kernel.log`, exit 0
  (session 60758 terminal); no type-in-type, unsafe fixpoints or assumed
  positivity.
- The two witness theorems retain four inherited classical/extensionality
  assumptions. Neither adds an external-call, execution or output assumption.

The earlier elaboration needed an explicit Clightdefs import and an explicit
block argument. The failing tactic goal was inspected with Show. These fixes
do not modify the statement or weaken its conclusion.

## Repair candidate and outstanding work

The attached isolated worktree
`/Users/brenorb/.codex/worktrees/frame-memory-contract/simplicity` starts at
`3fbfa722`. Its candidate changes only the shared frame-object exclusive-end
bound to `base + 16 <= Ptrofs.max_unsigned + 1`. All C and canonical Haskell
sources remain unchanged. Pointer-field starts still fit within max_unsigned;
the existing frame layout/address/evaluation/assignment lemmas compile with
the wider domain.

The full candidate audit is running in
`/tmp/jet-frame-memory-candidate-audit.log`, session 60362. This is snapshot
generation with an actual rebuild, kernel checking and AST comparisons; it
is **not final acceptance**. No candidate proof or snapshot is integrated or
published. After completion, inspect every changed public type/definition/
assumption, then run a separate --accept without update/no-build flags.

Next obligations:

1. Rebuild all consumers of the widened predicate and check their whole public
   conclusions; repair any caller requiring the unnecessarily strict end bound.
2. Review analogous exclusive-end bounds on UWORD output ranges and environment
   objects, distinguishing pointer starts from exclusive byte endpoints.
3. Establish the legitimacy and reachability/domain of initial representations
   and separation/address premises; local equivalence is not a constructor proof.
4. Complete the remaining per-jet definition/hypothesis/canonical-chain review.

The registered inventory remains 347/533, with 104 explicit libc conditions.
The review matrix still has 26 reviewed local contracts and 284 registered rows
requiring further evidence. All local review statuses retain the shared memory
and constructor boundaries described in their reports.
