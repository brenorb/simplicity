# Jacobian infinity predicate: compiled public candidate

Final theorem: `C.jet_secp_gej_predicate_local.gej_is_infinity_literal_local_spec`.
It freshly compiles as 89446, terminal exit 0. This is a complete formal
implementation-to-program candidate, not yet accepted registry coverage.

## Specification and domain

The target is `literal_gej_is_infinity = drop canonical_fe_is_zero`, the
canonical `LibSecp256k1.gej_is_infinity = drop fe_is_zero` program. The field
zero program is the existing canonical Simplicity combinator port, not a
numeric replacement. Algebra-independent parametricity is formally proved.
The input is `((Word256, Word256), Word256)` and the output is one Simplicity
bit. All three inputs are arbitrary, including noncanonical field encodings.
No extra operand bound or zero-only domain is imposed.

The theorem uses the existing complete `secp_jet_local_spec` frame contract:
arbitrary valid source frame base/cursor, representability through all 768
input bits, represented encoded input, writable one-bit output space, output
cells/prefix/cursor and permitted outside-load observations. Coordinate input
segments are derived from the encoded product by the existing append lemma,
not exposed as extra final preconditions. Word-boundary crossings are covered
by the reused original coordinate reader proofs, not excluded by alignment of
logical bit cursors. The source C struct itself retains its legitimate
alignment requirement.

## Actual execution chain

The public generated `f_simplicity_gej_is_infinity` is executed with its exact
parameters, local declarations and initial undefined `_t'1` temporary. The
proof derives both real local allocations (16-byte source frame and one
128-byte point), actual by-value source copy, original `read_gej`, original
flag accessor, original one-bit writer, true return/cast and actual free_list
of both locals. Coordinate reads use offsets 0/40/80 inside the single point
allocation. The original Z zero-test and final flag store are derived from
owned memory; no fictitious coordinate allocation is assumed.

Final theorem premises do not assume intermediate C calls, canonical limb
loads, flag/output values, source cursor updates, stores or freeing. Internal
compositional wrappers do take calls, but the owned/public results discharge
every one from initial frame/storage facts. Output prefix and permitted memory
observations are formally proved, not comments or testing substitutes.

The final theorem has six inherited execution assumptions: classical choice/
logic, dependent functional extensionality and CompCert external/inline
assembly semantics. No new assumption or `memcpy_model` is introduced.
Compiled literals/parametric proofs are closed under the global context.

## Remaining acceptance work

The 22-module archive has 62 completed compiled results. Earlier 57 results
have independent whole-closure kernel receipts, most recently 85424 exit 0.
Independent final public kernel **88320 also passed, terminal exit 0**, with
the exact unchanged 15-name context allowlist and all unsafe categories empty.
All 62 results have whole-closure kernel evidence; standard acceptance remains
separate. Complete result/definition inventories and preliminary deep printing
are recorded in `SNAPSHOT-REVIEW.md`.

Source-correspondence/mutation gates, reviewed standard type/definition/axiom
snapshots, isolated fresh full acceptance and guarded checkout integration
remain required. The candidate depends on the separately archived point-
infinity layout/lifecycle support and shared field-add reader rebase module.
Acceptance must reconcile those dependencies with newer checkout metadata,
not overwrite inventories/snapshots from the older isolated baseline. No new
registry entry, checkout proof input, C source or Haskell specification has
been changed by archiving this candidate.
