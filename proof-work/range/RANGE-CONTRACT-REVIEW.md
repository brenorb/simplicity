# Range correction: scoped contract review

Status: reconciled candidate fully accepted (54683, exit 0); all 149 guarded
changes integrated exactly on `codex/range-integration`, with a matching full
proof-input fingerprint. The subsequent original checkout acceptance (24458)
also passed; it covered additional unrelated checkout inputs.
Coverage remains 349/533.
The complete original range candidate plus 26 repairs compiles; the current
18 accepted odd/zero sources compile unchanged against its dependencies and
their full public chains pass independent kernel checking. Exact receipts and
source hashes are in `CONTINUATION.md`.

## Semantic change and old inputs

The only changed frozen semantic definition in the complete printed comparison
is `write_frame_at`. Its old blanket `bf <> bw` is replaced by, for every output
word that can be accessed from the initial capacity:

```
bf <> bw \/ word_address + 8 <= base \/ base + 16 <= word_address
```

This excludes overlap of output words with either metadata field, but permits
disjoint subobjects in one CompCert block. Count/cursor bounds, valid metadata,
writable cursor and output-word permissions, representable output addresses,
and initial word loads remain required. Source/input separation is not removed.

`range-domain-review.v.source` formally proves inclusion of the exact accepted
predicate, renamed solely to allow both definitions in one module. All old
inputs imply the candidate predicate. Its complete module and dependency chain
pass compilation and kernel checking; it adds no assumed execution or output.

`range-embedded-review.v.source` additionally constructs a 24-byte allocation
with metadata at [0,16) and an arbitrary initial word at [16,24). The candidate
predicate accepts all 64 cells, whereas the accepted blanket-separation
predicate rejects that same memory. The candidate's actual C writer executes
for either Boolean and proves the output bit, cursor, prefix, outside-range
loads and permissions. Compilation and independent kernel checking pass.
This is helper-domain evidence, not a new jet registration or evaluator proof.

`range-one8-review.v.source` additionally constructs a complete arithmetic-jet
call through the candidate's existing arbitrary-layout `one_8` theorem. It
derives the by-value source-frame bytes, allows source and destination metadata
to alias, and concludes actual C execution, canonical output, cursor 56, prefix
and outside-memory preservation. Compilation and whole-chain kernel checking
pass. This concrete cursor-64 witness supplements the general theorem; it does
not generalize the evaluator's reachable states or add registered coverage.

## Changed audited support interfaces

The complete reconciled printer checks 3,583 results and 1,823 frozen definitions.
Of the 3,577 existing types, 3,559 are unchanged and 18 change:

| Interface group | Changed existing results | Reviewed change |
| --- | ---: | --- |
| Short/aligned/source-crossing copy helpers | 8 | Replace metadata/output block inequality by separation of the actual head word. |
| Two-destination-word copy helpers | 3 | Require range separation for both accessed destination words; old distinct blocks imply both alternatives. |
| Prefix/output-cell preservation | 3 | Replace block inequality by separation at the preserved word, indexed for a list of cells. |
| Raw Bitcoin write32 | 1 | Replace metadata/output inequality by head-word range separation. |
| Small memcpy helpers | 2 | Require actual head or head/lower range separation; retain explicit `memcpy_model` and source/copy separation. |
| Wide-copy numerical bounds | 1 | Remove obsolete `bd <> bw` from `wh_bounds`; retain all numerical bounds. |

The 17 execution/preservation results retain their outer conclusions byte-for-
byte modulo printer whitespace. The changed numerical `wh_bounds` is not an
execution theorem or public jet contract. Its removed separation fact is
replaced at its actual consumers by `wh_metadata_range`, derived from initial
capacity at the first and last accessed words. For 65..128-bit copies their
spacing bounds preclude fitting a 16-byte metadata object between the words;
the helper retains real memory operations and its execution conclusion.

Six additional range/preservation support results are audited; no jet is added
by them. No canonical frozen definition changes appear. The same public jet
conclusions now use the widened shared frame domain. Compilation and snapshot
comparison alone do not establish all canonical or domain review obligations.

## Explicit remaining obligations

1. The reconciled 3,583-result assumption audit passes: all 3,577 existing sets
   are unchanged and the six additions use only the four inherited classical/
   extensionality assumptions. The value/hash whole-chain kernel check also
   passes, completing all 44 repaired-module receipts. Preserve these exact
   reviewed sources and records during final assembly.
2. The exact reconciled candidate is assembled with all accepted predicate
   sources, checkers, registrations and reviewed snapshots. Its same-tree build
   passes; the odd/zero extension is preserved, not replaced by older metadata.
3. Independent candidate acceptance passes without snapshot-update flags:
   complete build, 603 kernel modules, assumption/contract gates, negative
   fixtures and all four original-source AST comparisons. All 149 integrated
   target hashes equal this candidate; separate actual-checkout acceptance is
   running with preserved unrelated inputs. See the current continuation receipt.
4. Keep other domain issues open. In particular output words still use the
   exclusive-end bound `addr + 8 <= Ptrofs.max_unsigned`; this review does not
   justify that bound or prove every valid allocation/representation reachable
   from the evaluator. Primitive-environment and constructor-domain review,
   and exhaustive individual canonical correspondence review, remain separate.

The C library, canonical programs, target configuration and accepted snapshots
are unchanged during this review. Conditional libc results remain conditional.
