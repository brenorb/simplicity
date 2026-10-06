# Per-contract review: inherited Bitcoin TimeLock, totals and fee

This is a source/definition/precondition/conclusion review of **12 existing
registered contracts**, at proof tree `4888ca77` (unchanged by documentation
commit `1f6d49b0`). It adds no jet equivalence. The result is a complete local
jet chain under the stated initial frame/environment representations; it does
not prove the transaction constructor establishes those representations.

No new discrepancy was found in these 12 chains. Remaining constructor and
global review scope must not be inferred from this conclusion.

## Canonical binding and chain, one row per contract

All names below are `simplicity_bitcoin_<suffix>`. The public theorem has the
same suffix prefixed by `bitcoin_` and suffixed by `_local_spec`.

| C suffix | Catalog/program | Public module | Canonical/output bridge | Initial environment boundary |
| --- | --- | --- | --- | --- |
| `tx_is_final` | `TxIsFinal`, `TimeLock.txIsFinal` | `jet_bitcoin_is_final_local` | `bitcoin_tx_is_final_spec_value`, `encode_fromBool`; actual `writeBit` call | `bitcoin_tx_is_final_env_rep`: cached isFinal equals forallb of the logical input sequences |
| `tx_lock_height` | `TxLockHeight`, `TimeLock.txLockHeight` | `jet_bitcoin_lock_local` | `bitcoin_lock_program_value true`, `lock_result_value`; actual lockHeight/write32 calls | `bitcoin_lock_env_rep`: isFinal cache and exact Word32 locktime |
| `tx_lock_time` | `TxLockTime`, `TimeLock.txLockTime` | `jet_bitcoin_lock_local` | `bitcoin_lock_program_value false`, `lock_result_value`; actual lockTime/write32 calls | Same initial lock representation |
| `tx_lock_distance` | `TxLockDistance`, `TimeLock.txLockDistance` | `jet_bitcoin_distance_local` | `bitcoin_lock_distance_program_value true`, `dist_result_value`; actual lockDistance/write16 calls | `bitcoin_distance_env_rep`: count, index, version and sequences; valid current index derived from Bitcoin.env |
| `tx_lock_duration` | `TxLockDuration`, `TimeLock.txLockDuration` | `jet_bitcoin_distance_local` | `bitcoin_lock_distance_program_value false`, `dist_result_value`; actual lockDuration/write16 calls | Same initial distance representation |
| `check_lock_height` | `CheckLockHeight`, `TimeLock.checkLockHeight` | `jet_bitcoin_check_lock` | `bitcoin_check_lock_program_value true`, `lock_result_unsigned`; actual read32/lockHeight/comparison | `bitcoin_check_lock_env_rep`, an existential initial lock representation |
| `check_lock_time` | `CheckLockTime`, `TimeLock.checkLockTime` | `jet_bitcoin_check_lock` | `bitcoin_check_lock_program_value false`, `lock_result_unsigned`; actual read32/lockTime/comparison | Same initial check-lock representation |
| `check_lock_distance` | `CheckLockDistance`, `TimeLock.checkLockDistance` | `jet_bitcoin_check_distance` | `bitcoin_check_distance_program_value true`, `dist_result_unsigned`; actual read16/lockDistance/comparison | Initial distance representation; valid-index test discharged |
| `check_lock_duration` | `CheckLockDuration`, `TimeLock.checkLockDuration` | `jet_bitcoin_check_distance` | `bitcoin_check_distance_program_value false`, `dist_result_unsigned`; actual read16/lockDuration/comparison | Same initial distance representation |
| `total_input_value` | `TotalInputValue`, `Transaction.totalInputValue` | `jet_bitcoin_totals_local` | `bitcoin_total_input_value_spec_sum`, `decode_wide64_unsigned`, `fw6_mod64`; actual cache load/write64 | `bitcoin_total_input_value_env_rep`: cached total matches logical sum modulo 2^64 |
| `total_output_value` | `TotalOutputValue`, `Transaction.totalOutputValue` | `jet_bitcoin_totals_local` | `bitcoin_total_output_value_spec_sum`, `decode_wide64_unsigned`, `fw6_mod64`; actual cache load/write64 | `bitcoin_total_output_value_env_rep`: same modular correspondence for outputs |
| `fee` | `Fee`, `Transaction.fee` | `jet_bitcoin_fee_local` | `bitcoin_fee_spec_value`, `fw6_sub`, `fw6_sub_mod64`; actual unsigned subtraction/write64 | `bitcoin_fee_env_rep`: both cached totals correspond modulo 2^64 |

The catalog bindings are at `Haskell/Simplicity/Bitcoin/Jets.hs:185–218`.
Literal definitions are in `Haskell/Simplicity/Bitcoin/Programs/TimeLock.hs`
and `Programs/Transaction.hs:79–87`. The Coq public propositions are the
entire application contract, not that contract under an extra execution,
desired-output or impossible premise. `Check` output for all 12 was recorded
in `/tmp/jet-inherited-bitcoin-values-review-compile.log`.

## Expanded conclusions and legitimate domain

For all represented initial memory/frames and all logical inputs, the eight
getter contracts conclude existence of a real `Clight2.eval_funcall` in
`bitcoin_ge`, E0, true return, canonical encoded output, preserved write prefix,
exact destination cursor decrement and unchanged loads outside the stated
footprint on blocks valid in the initial memory.

The four checks use **application_jet_partial_spec**, whose existential memory
and actual execution are conclusions on *both* success and failure. Return is
`jet_partial_return (spec input environment)` without a success premise.
On success the Unit output, prefix and unchanged destination cursor follow;
outside-footprint framing also holds on failure. Their actual proofs establish
the stronger preservation of all original loads, since only the local source
copy is read/updated. No output value is specified after assertion failure.

The input Word32/Word16 types are unrestricted. Version is interpreted as
unsigned Word32, including the high bit. Locktime preserves the strict
500000000 split; relative locks preserve version >=2, disable bit31, selection
bit22 and the low16 payload. `currentSequence` is the canonical
CurrentIndex/assert(InputSequence) composition. An invalid current index is
excluded by the canonical environment constructor (`primEnv`), not by a
jet-specific success assumption. The explicit initial count/index relation
derives the actual C precheck and avoids the helper's assertion-fail branch.

`sigTxInBounds`/`sigTxOutBounds` retain the uint32 count range, matching the
original raw transaction API (`C/include/simplicity/bitcoin/env.h:53–54`).
Nonempty inputs follow from a valid current index. Zero outputs remain legal.
These count bounds describe representable inputs to this C target, not the
entire set of arbitrarily constructed Haskell vectors. No monetary range,
positive fee or no-overflow assumption is used. Signed Coq amount representatives
encode all Word64 values; `jet_bitcoin_value_domain.v` proves unsigned-sum
correspondence. Totals and fee wrap modulo 2^64, including underflow.

The common initial frame predicates require valid addresses, source encoding,
representable cursor movement and writable output capacity. The footprint
separation on cache getters prevents the writer from overwriting fields still
needed by the call. The checks need no additional environment/output separation
because they write only their fresh local copy. These are memory contracts,
not narrowed numeric input domains.

## Execution and lifecycle premises are discharged

The generic section lemmas have helper execution hypotheses. The 12 public
specializations discharge them:

- Real `f_lockHeight`/`f_lockTime` are definitionally equal to the inspected
  `lock_fn` bodies (`f_lockHeight_shape`/`f_lockTime_shape`). `eval_lock_fn` derives
  their execution from actual initial loads; public specializations apply it.
- Real `f_lockDistance`/`f_lockDuration` are definitionally equal to the actual
  generated bodies, including the assertion branch. `eval_dist_fn` derives
  their execution; valid current index is derived before its application.
- `bitcoin_read_wide_step` derives read16/read32 calls and exact unsigned return
  from the initial encoded cells. It preserves the caller's original loads.
  The helper is transported using checked symbol/function correspondence and
  `fundef_okb`, not by assuming a new Bitcoin execution relation.
- `bitcoin_write_wide_step`/`bitcoin_writeBit_step` derive actual writer calls
  from output capacity, then supply their concrete output/framing effects.
- `bitcoin_wrapper_layout` and its simple corollary derive allocation of the
  16-byte local, the actual By_copy frame assignment, function entry, return
  and final `Mem.free_list`. Freeable permission is preserved by the body and
  used to derive freeing; freeing is not a public precondition.
- `bitcoin_bool_wrapper` does the same for both boolean return values and
  derives preservation through local allocation, read and freeing.

The mid-execution predicates are proven inside the public proof from its initial
conditions. They are not premises of the final registered theorems.

## Literal program definitions reviewed

The comparison followed these transitive ports, rather than accepting a numeric
formula as the specification:

- `for_while_program`: SingleV executes counters false then true, stopping on
  Left; DoubleV nests high/low loops with the literal tuple routing. Compared
  with `Programs.Word.forWhile:359–363`.
- `final_program` and `predicate_spec`: canonical InputSequence/all loop,
  missing-index success and first non-final early exit. The list reduction is
  proved from the literal loop, not its replacement.
- `total_program`: canonical InputValue/OutputValue loop and accumulator;
  `total_adder` at Word64 is `false &&& iden >>> fullAdder >>> ih`, matching
  Haskell `add word64 >>> ih`. FullAdder recursion, maj and xor3/xor_xor match
  the Haskell full_add/Bit compositions. The Word1 adderBit special case is not
  substituted into this Word64 program.
- `fee_tail`, `subtract_word_spec`, full subtraction and complement: input
  minus output, borrow/payload structure, then payload projection.
- `parse_lock_spec`, `parse_sequence_spec`, `le_word_spec` and Bit combinators:
  exact projections, branch direction, threshold, inclusive comparison and
  low16 representation.
- `bitcoin_assert_spec`: pair with unit and assertr of canonical cmrFail0;
  Haskell `fail0 = fail (hash0, hash0)` and its commitment root agree with the
  Coq assertion pruned-branch construction.

## Cache boundary and verification evidence

The initial predicates require physical caches to correspond to the logical
transaction. These are explicit initial data-representation facts. The source
constructor initializes isFinal true and clears it for a non-final sequence,
and accumulates uint64 totals (`C/bitcoin/env.c:96–116,152–156`). This source
inspection supports the intended correspondence; **no complete Clight proof of
the constructor is claimed**. None of these predicates contains a jet call,
final output frame or assumed final memory.

All seven public modules are byte-identical between the current branch and the
accepted review worktree; their compiled artifacts are newer than their
sources. The previous full acceptance checked these modules and their
dependencies. All 12 public results retain only the same six inherited
Coq/CompCert assumptions; they have no extra memcpy/global/helper premise.

Fifteen closed semantic boundary diagnostics were added only in
`/Users/brenorb/.codex/jet-proof-scratch/original-c/review_inherited_bitcoin_values.v`:
locktime just below/at the split, final transaction, maximum Word32 locktime,
sequence disable/selection/payload, version high bit, positive fee, underflow,
high-bit amount and wraparound. They evaluate the actual canonical Coq program
definitions. The complete file compiles with exit 0 and its separate coqchk
passes with exit 0, including no type-in-type, unsafe fixpoints or assumed
positivity. Logs:

- `/tmp/jet-inherited-bitcoin-values-review-compile.log`
- `/tmp/jet-inherited-bitcoin-values-review-kernel.log`

The first diagnostic run failed at elaboration because imported Bit.true
shadowed the bool constructor; explicit Datatypes constructors corrected that
namespace error. No unfinished proof was compiled or accepted. Boundary examples
supplement the source/contract/derivation review; they do not replace the
universally quantified public proofs.

## Inventory interpretation

At this review, `JET_EQUIVALENCE_REVIEW_MATRIX.csv` had all 533 public declarations: 12 local
contracts reviewed here; 36 prior full-shift family reviews; one prior complete
fe_normalize chain; 298 registered entries still needing evidence cross-reference;
and 186 without final registrations. These statuses are not 49 newly accepted
proofs and do not enlarge the 347-entry registry.

The subsequent `JET_BITCOIN_SIMPLE_GETTERS_REVIEW.md` reviews six more existing
contracts: the current matrix has 18 reviewed local contracts and 292 remaining
registered rows requiring evidence cross-reference. Coverage is unchanged.

`JET_INHERITED_DECLARATIONS.csv` indexes declaration locations and current source
hashes across all 122 inherited `.v` modules and four generation inputs. It
includes all individually registered public names from those modules. Its
lexical declaration groups are a review index, not a replacement Coq parser or
proof of exhaustive transitive dependency coverage. In-reviewed-chain-scope
means a module participates in these chains; it does not certify all its
declarations. Generated AST declarations are distinguished from proof support.

Global inherited fidelity review remains partial. Next review targets are the
remaining registered Bitcoin getters and the SHA/composed-hash boundaries.
