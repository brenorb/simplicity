# Original point-negate preliminary contract review

78 types and 20 definitions match exactly modulo whitespace. Two helper
prefix types and six computed definitions need deep supplements, with every
retained ordinary-depth fragment appearing in order. This is an ellipsis
diagnostic, not a certificate of equality of omitted terms; archived sources
and independent kernel checking remain essential. The reviewer requires the
specific observed difference sets, not any arbitrary set of changed terms.

The final theorem is `secp_jet_local_spec f_simplicity_gej_negate` on the
full Word256 triple, with the same Word256 triple output and literal
`take ge_negate &&& drop fe_normalize` target. Its unchanged inherited local
contract quantifies over the actual input values, requires the source frame,
representable read cursor and writable output frame, and concludes actual
Clight call returning true, encoded output, preserved prefix, final output
cursor and permitted unchanged loads. No point-membership restriction,
assumed intermediate call/output/free, or replacement numeric target is added.
The public execution proof derives the original two allocations, source copy,
reader/weak-normalize/field-negate/writer calls, true return and both frees.

Reviewed literal definitions retain the actual pair/take/drop structure and
existing literal field-negation port. The five-field record and bounded writer
adapter are internal representation contracts; their bounds are discharged
from actual read/helper storage in the public proof, not assumed publicly.
The two old call-premise adapters remain internal lemmas; the owned/public
composition discharges their calls. Field and source ownership/framing are
transported across the current memory, rather than reused from old memories.

40 results are closed under the global context. The union of actual per-result
axioms is precisely the six inherited execution assumptions; the final public
theorem has all six. No memcpy/library model or additional assumed declaration
appears. Literal GE/GEJ and normalize parametricity are closed. Whole imported
kernel context has its separately recorded fifteen-name inherited inventory
and empty unsafe categories; this is distinct from per-result axiom sets.

Reproduce read-only review and its in-memory parser fixtures:

Next assemble the exact candidate into normal project load paths, include the
reviewed definition/result inventories and scoped source gate/tests, generate
and review full standard snapshots preserving every inherited record, then
run full isolated acceptance with no update/no-build flags. Guard integration
against the newer staged/dirty checkout. General evaluator-domain frame
obligations remain; this local contract does not close those broader goals.
