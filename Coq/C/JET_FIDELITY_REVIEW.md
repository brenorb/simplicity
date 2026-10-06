# Canonical specification fidelity review

The implementation/configuration target is fixed in `JET_TARGET.md` and
`jet_source_target.tsv`. The compiled proof inventory is not itself a fidelity
certificate. This review records corrected differences and the remaining chains required
before experimental support can count as final equivalence coverage.

## Verified target correction

The added `copyWords` helper is absent from C and all four regenerated ASTs.
One-word and two-word copy execution uses the actual external memcpy declaration.
The strengthened libc contract requires valid source/destination blocks, readable
bytes, writable ranges, positive representable sizes, non-overlap and ranges
without pointer wraparound. The three application sites derive those facts from
existing preconditions and compile. No canonical copy conclusion is weakened.
Four regeneration comparisons and the 96 native C correctness tests pass.

## Bitcoin environment domain discrepancy

The legacy `Simplicity/Primitive/Bitcoin.v` defines its fee as total output minus
total input, and requires that value to satisfy `moneyRange`. The canonical
Haskell `Bitcoin/DataTypes.hs` defines `txFee` as total input minus total output.
This is an actual domain restriction, not a printing/qualification difference.

A checked diagnostic in `/tmp/jet_canonical_env_counterexample.v` proves that no
legacy Coq `sigTx` can have total input 10 and total output 9. It is closed under
the global context, compilation exit 0, with log
`/tmp/jet-canonical-env-counterexample.log`. Such a positive fee is permitted by
Haskell's `primEnv`, whose constructor checks only that the current index is
in range. The C transaction constructor in `C/bitcoin/env.c` does not impose the
legacy monetary-bound fields either.

The legacy type also requires positive output count and constrains signed
64-bit amounts and aggregate amounts by MAX_MONEY. Haskell stores `Word64`
amounts and does not impose those restrictions in `primEnv`; the C constructor
copies uint64 amounts and accumulates totals. These differences required correction of the Coq mirror and its representation
lemmas using exact unsigned-word semantics and modular arithmetic. The canonical
Haskell programs remain pinned and unchanged; the final output/failure/memory
conclusions are preserved.

The monetary proof fields have now been removed, empty output lists admitted,
and the fee direction corrected. The amount-reading proofs use an unconditional
signed/unsigned Word64 equality. Total and fee cache representations compare
modulo 2^64, including aggregate overflow, rather than imposing equality with an
unbounded integer. `jet_bitcoin_value_domain.v` proves the unsigned-sum bridge
and constructibility of positive-fee, zero-output and high-bit inputs. Targeted
compilation passes in `/tmp/jet-bitcoin-domain-callers.log`,
`/tmp/jet-bitcoin-modular-totals.log` and `/tmp/jet-bitcoin-value-domain.log`.

The registered Bitcoin getter definitions and representations have been reviewed
against the pinned primitive semantics. Initial cache correspondence is explicit
and does not assume execution or output. Experimental composed hash programs
still require the bridges listed below; their names and compilation alone do
not establish canonical equivalence.

## Extended Bitcoin primitive semantics

The free cached-hash interface in `jet_bitcoin_ext_prim.v` is retained as an
auxiliary representation. `jet_bitcoin_raw_env.v` now defines the raw input
scripts/annexes/scriptSigs, tap fields and non-witness transaction serialization.
Its independent primitive semantics computes script hashes and double-SHA256
transaction id, following pinned `Bitcoin/Primitive.hs` and
`Bitcoin/DataTypes.hs:294–322`. The kernel-checked projection lemma relates all
eight extended primitive constructors to that raw semantics, including both
out-of-range lookup and missing-annex branches.

`jet_bitcoin_raw_jets.v` lifts eight existing execution/output/framing contracts
through that projection. Six are primitive getters; the two current-input hash
programs preserve `CurrentIndex >>> assert (InputX)` and its Option failures.
The whole module compiles with exit 0 in `/tmp/jet-bitcoin-raw-jets.log`.
Seven existing coverage rows now use the raw contracts; tappath remains
unregistered pending the wider review. Cache-only `ext_environment` contracts
are no longer accepted by the coverage metadata gate.

The raw semantics allows arbitrary tap paths. Projection at the initial C
representation boundary requires length <=128, matching the actual rejection in
`C/bitcoin/env.c:192`; no execution or output fact is assumed. Cached fields must
encode the computed logical hashes. The C transaction constructor copies the
caller-supplied `rawTx->txid`; this work does not claim that constructor computes
or verifies transaction serialization. Its canonical txid correspondence remains
an explicit initial representation requirement.

The interface review also found and corrected the legacy base LockTime name
`locktime` to canonical `lockTime`, which changes its commitment tag. The identity
gate now checks all shared base constructors as well as the extended signature,
and requires the union to cover the canonical constructors. Compatibility-only
base constructors for composed/legacy programs are explicitly auxiliary.
Regression tests reject altered base names/types and missing constructors.

The full final kernel, assumption and contract acceptance passes (exit 0)
against the reviewed snapshots, without update flags. The remaining composed hash programs
are not promoted by these raw bridges; integer models and symbolic trees also
remain auxiliary.

## Experimental support reviewed so far

The inputHash port follows the pairing/case/assertion composition in the pinned
Bitcoin SigHash program. TimeLock distance/duration and their assertions retain
the canonical version check, parseSequence branches and word comparisons.
Total-value and fee programs use the literal forWhile/add/subtract composition;
their environment-domain issue above is corrected. TapData/TapLeaf/
TapBranch constants have checked canonical hashBlock computations and padding
byte equalities. Review globals, dispatch and environment representations at the
C boundary before promoting any of these results.

The symbolic executor retains actual Clight execution in its soundness theorem
and its oracle correctness predicate. Read8s/write8s oracle proofs, memory-region
separation, integer interval analysis, normalization and byte/limb lemmas have
compiled on the original C. The field-normalization integer model and byte/limb
results are reused in the complete canonical `fe_normalize` chain accepted below. Their individual
statements remain support and do not each count as jet equivalence. Additional
mathematical field properties alone do not close other jets.

## Acceptance status

The conservative registry is 347/533: 243 entries without an extra libc
premise, 104 explicitly conditional on libc, and 186 unregistered declarations.
No experimental result is promoted solely because its name says it proves a jet.
The support inventory is broader than the coverage registry.

The separate final acceptance passes (exit 0), including all 583 kernel modules,
3,534 public assumption records, contract/definition snapshots, negative tests,
and four independently regenerated ASTs. There are 1,834 closed public results.
All common public assumption records retain their previous axiom sets; no new
axiom name or library-level axiom is introduced. Four obsolete `copyWords`
execution/linkage lemmas are retired, and reusable memory support is retained.

Review of every changed existing lemma/theorem statement finds 92 restored
final libc premises, 12 helper premises and five adaptations to the genuine
external-call ABI/body. Their output/framing conclusions are preserved. The
additional semantic changes are the expanded Bitcoin value/output domain,
modular cache representations, canonical fee direction/name, and raw-data
projection described above. The final acceptance run compares the reviewed
snapshots without updating them and completes with exit 0. The consolidation
retains experimental results as checked support under their actual statements,
with the 27 previous registrations and the one canonical field registration
justified below. See `JET_ACCEPTANCE.md`
for the receipt and candidate/final fingerprint distinction.



## Canonical continuation reviewed and accepted

The twelve `jet_core_fullshift64_jets.v` statements retain the literal
`Word.full_left_shift1` / `full_right_shift1` programs. The pinned catalog's
`full_shift` compareVectorSize/vectorComp dispatch selects exactly their Coq
specializations. Their actual original-C two-word copy retains explicit libc
and initial-frame/output/framing obligations. All 36 narrow/wide bindings and
literal recursions are checked by the new negative-tested source gate.

Fifteen Bitcoin contracts are now registered after review: raw tappath, two raw
annex getters, totals/fee and nine TimeLock contracts. The full Word64/modular
value domain is preserved. Current annex applies the canonical outer assertion
while retaining the inner absent-annex success. The four check-lock assertions
use the entire `application_jet_partial_spec`, preserving option-dependent C
return, successful output/prefix/cursor and framing on both success and failure.
Metadata rejects added impossible premises or the wrong linked program/env.

All old snapshot records are unchanged; three raw annex results and five new
frozen definitions are added. The final log is
`/tmp/jet-next-canonical-final-accept.log`, exit 0. Its snapshot-inclusive
SHA-256 is `a566e6bfc17b188b9377c0993284b555f6364e56f8c17801833d4b0e203572b6`.

## Canonical original-C field normalization accepted

`fe_normalize_local_spec` now establishes the complete original public function
contract against the literal canonical `fe_normalize` program. The source gate
checks its catalog dispatch, full FE=Word256 domain, exact field order,
subtraction and conditional port, and equality with the common quantified
frame/memory contract after only replacing `ge0` by the actual `secp_ge`.

The proof derives real read8s/set-b32/normalizer/get-b32/write8s calls and their
memory representations, including inputs at and above the field order. It
derives entry allocation, the actual By_copy frame assignment, local ownership
and final free_list from the legitimate initial frame contract. Successful C
return and canonical encoded output/prefix/cursor/framing are all conclusions.
No execution, intermediate output, or final Freeable premise is assumed by the
public theorem. It retains the same six inherited Coq/CompCert axioms and no
extra libc model.

Snapshot review preserves every old assumption set, type and frozen definition.
The 200 new records comprise one final jet and 199 support results; 151 are
closed. The separate final acceptance is `/tmp/jet-secp-normalize-final-accept.log`,
exit 0, snapshot-inclusive hash
`5d01956807ea2f325ca099e65818f5e23d521e31ac994863c1f5fd09deeb6eae`.
The candidate hash excludes the snapshots and is recorded in `JET_ACCEPTANCE.md`.
C and canonical Haskell sources, target flags and the external memcpy mechanism
are unchanged.

The next `fe_is_odd` and `fe_is_zero` full public proofs exist only in the
isolated scratch namespace. Their ports preserve `fe_normalize >>> lsb256` and
the canonical zero-or-field-order test respectively. Compilation, kernel and
actual statements/assumptions were reviewed. They are not registered or accepted
in this round; a subsequent candidate/snapshot review/separate acceptance is
still required. No coverage is claimed for scalar helper support.

## Remaining proof queue

SHA contracts use the actual generated SHA translation unit and explicit
`sha_globals_ok` (portable compression dispatch and max-counter load). The AST
initializers are respectively `Init_addrof _sha256_compression_portable 0` and
`Init_int64 2^61`, matching the C source. A checked global-initialization and
preservation bridge is still needed before treating all of these premises as
derived facts under the target program's startup state. Canonical raw-data lifts
of the composed Bitcoin hash programs also remain outstanding. Merely accepting
more global-environment names in the coverage parser would not discharge them.

The source inventory also lists two unregistered public secp declarations,
`off_curve_scale` and `off_curve_linear_combination_1`. Report the distinction
between 533 header declarations and their actual jet-node registrations when
finalizing the coverage denominator; do not silently erase those functions from
the missing-work report.


The initial corrected audit `/tmp/jet-bitcoin-raw-candidate-audit.log` failed
at coqchk with `Fatal Error: Stack overflow`. The native OCaml 4.14.1 arm64
checker inherited an 8,176 KiB stack limit. Repeating the complete candidate run
with 65,520 KiB passes, log
`/tmp/jet-bitcoin-raw-candidate-stack64-audit.log`, exit 0. `check-jets.sh` now
raises a smaller soft limit to that verified size, or fails if the OS hard limit
prevents it. No kernel check, proof premise or C/compiler flag is changed by this
resource adjustment. Final acceptance log:
`/tmp/jet-consolidation-final-accept.log`, exit 0; the final kernel run also
passes using the script's automatic resource adjustment.

The Nix source expressions parse successfully. A Nix derivation build and remote
CI run have not been performed locally; do not infer them from the native audit.
