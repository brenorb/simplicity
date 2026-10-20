# Null-data parser fuel, literal encodings and complete C endpoint

## Formal progress required by source fidelity

The canonical Haskell parser loops until empty; the Coq port has termination
fuel. `getTxNullDatum_consumes` proves that every accepted datum consumes an
opcode byte, including zero-length immediate pushes. The soundness/completeness
and fuel-adequacy theorems identify the bounded port with `null_data_parse`, an
unbounded successful-parse relation with exactly the empty and one-datum rules.
`txNullData_parser_relation` adds the required OP_RETURN prefix. No successful
parse is lost because the supplied input-length fuel runs out.

`haskell_encode_null_datum` mirrors all22 canonical constructor encodings,
including the two-bit push selector, four-limb big-endian hash conversion,
negative/reserved bit and all16 four-bit small values. The encoding bridge
reuses the checked Haskell State-word and hash/word bridges, not a new ad hoc
integer specification. `elements_output_null_datum_literal_matches` covers both
index lookups, parse failure and both nested presence tags.

The shared `application_jet_bitmachine_spec_pointwise` transports an already
proved whole C contract through a pointwise specification equality.
`elements_output_null_datum_literal_bitmachine_spec` discharges that premise
with the checked C theorem: actual entry, source copying, readers, every output
alternative, return conversion/free and preservation of represented frames.
It is not merely an equality of two specification functions.

## Scope

The environment representation remains input-independent and explicitly
requires the physical parser/cache correspondence. The real C environment
builder establishment proof is not supplied here. The public contract explicitly
uses represented/separated evaluator frames, not arbitrary overlapping buffers
or the broader old value-only application contract. The API-domain finding is
still open; see `../null-data-overlap-probe/README.md`.

These fuel/encoding proofs are supporting obligations for source fidelity, not
substitutes for the C execution proof or a formalization of the Haskell runtime
and host libraries. The separate `../elements-null-data-source/` gate reviews
the active canonical parser/encoding clauses and exact Coq/C contract. Its
source review is a separate receipt, not inferred from this compilation.

The pinned program is assertion-disabled. No main C, header, primitive,
registry or acceptance snapshot changed. Installed/accepted coverage is still
418/533, not419. Normal source/contract admission remains; the all-jet goal is
unfinished and no clean-HEAD reproduction is claimed for the dirty main tree.

## Verification

Fresh checker74587 exited0 with pinned Coq8.17.1 / CompCert3.14: explicit
compilation of all3 new modules, full reports for12 results and3 definitions,
Elements AST regeneration and recursive kernel checking. The definition report
also prints the inductive parse relation and both constructors; it is not omitted
by the usual Definition/Fixpoint-only inventory. Nine results are closed, the
literal bridge uses inherited functional extensionality, and the shared transport
and whole C endpoint retain the six inherited Coq/CompCert assumptions.

Independent evidence review22429 exited0 with41 rejected proof/evidence
corruptions. Revalidate its receipt/log/tool hashes and actual source/object
identities before committing. No axiom, admission or unchecked operation was
added. `canonical_source_gate_complete=false` correctly remains in this formal
batch: the separate source-review receipt supplies that later evidence.

Development corrections: bind source-list variables in Ltac patterns, qualify
`Datatypes.option_map` against an imported name, import the actual byte type,
annotate the shared transport's Set/Ty binders, provide a complete change target
and apply the inner list/drop rewrite after the parser result is exposed.
