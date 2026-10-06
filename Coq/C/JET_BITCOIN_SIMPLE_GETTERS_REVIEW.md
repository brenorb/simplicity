# Per-contract review: inherited Bitcoin simple getters and counts

This reviews six existing registered local contracts at proof tree `93542abc`:
version, lock_time, current_index, num_inputs, num_outputs and script_cmr.
It changes no proof, production C, canonical program or coverage registration.
The global inherited review remains partial. No discrepancy was found within
these six local chains under their explicit initial representations.

## Canonical binding, representation and execution chain

All C names below have the prefix `simplicity_bitcoin_`. All public theorem
names have the prefix `bitcoin_` and suffix `_local_spec`, except that
`lock_time` uses `bitcoin_locktime_local_spec`.

| C suffix | Canonical catalog/program | Public module | Initial fields and output bridge | Execution derivation |
| --- | --- | --- | --- | --- |
| version | `specificationTransaction Version = primitive Prim.Version` | `jet_bitcoin_version_local` | tx pointer at env+0; version at tx+464 equals unsigned logical Word32; `bitcoin_version_carrier_matches_primitive`, `wide_output_at_encode W32` | `bitcoin_transaction_version_canonical_spec` -> `eval_bitcoin_version_layout_matches_primitive` -> actual entry, By_copy assignment, field loads, linked write32 and free_list |
| lock_time | `LockTime = primitive Prim.LockTime` | `jet_bitcoin_locktime_local` | tx pointer at env+0; lockTime at tx+472 equals unsigned logical Word32; `bitcoin_locktime_carrier_matches_primitive` | `eval_bitcoin_getter32_layout` with actual body/interface and field-offset equalities discharged in the public proof |
| current_index | `CurrentIndex = primitive Prim.CurrentIndex` | `jet_bitcoin_current_index_local` | ix at env+48 equals logical envIx; `bitcoin_current_index_carrier_matches_primitive` | `eval_bitcoin_current_index_layout` derives its distinct actual wrapper body and linked writer call |
| num_inputs | `NumInputs = Prog.numInputs`; `firstFail word32 (primitive InputValue)` | `jet_bitcoin_count_local` | count at tx+448 equals length(sigTxIn); `bitcoin_transaction_num_inputs_spec_length`, `bitcoin_count_carrier_encoding` | Generic count adapter discharges canonical-search equality, actual getter body/interface and actual field offset |
| num_outputs | `NumOutputs = Prog.numOutputs`; `firstFail word32 (primitive OutputValue)` | `jet_bitcoin_count_local` | count at tx+456 equals length(sigTxOut), including zero; corresponding output-count bridge | Same adapter, specialized to the actual output-count function and field |
| script_cmr | `ScriptCMR = primitive Prim.ScriptCMR` | `jet_bitcoin_script_cmr_local` | taproot pointer at env+8; eight uint32 words at taproot+136 equal envScriptCMR; `encode_from_hash256` | Actual wrapper shape -> derived eight-word write32s run -> linked write32 calls -> wrapper return and free_list |

Canonical references inspected: `Haskell/Simplicity/Bitcoin/Jets.hs:196–221`,
`Programs/Transaction.hs:75–77`, and
`Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs:143–157`. C bodies are in
`C/bitcoin/bitcoinJets.c:67–79,194–198,208–213,292–303`. Physical field types are
from `C/bitcoin/txEnv.h`, not invented replacement structures. The accepted
`jets_bitcoin.v` is directly regenerated from the pinned C translation unit;
source-level body/interface/layout equalities select those generated functions.

## Definitions and complete public conclusions

The four primitive specifications are actual `Primitive.Combinators.prim`
terms. Counts use `bitcoin_transaction_num_inputs_spec`/`num_outputs_spec`,
which instantiate the literal `first_fail_program`; the legacy NumInputs and
NumOutputs Coq primitive shortcuts do not replace these programs.

The five scalar/count public propositions are the entire
`application_jet_local_spec` for the actual function and `bitcoin_ge`.
Script CMR uses the entire `application_jet_local_spec_sep` with its explicit
initial environment footprint. Their expanded conclusions quantify over the
initial memory and represented environment and establish:

- a final memory and canonical result, with actual Clight2.eval_funcall, E0
  and true C return;
- the exact canonical `encode` output, preserved write prefix and cursor
  decrement by 32 or 256 bits;
- unchanged loads outside the destination cursor/output footprint on blocks
  valid in the initial memory.

These six canonical operations succeed for every represented valid environment.
In particular the count searches cannot exhaust all Word32 indices: their
logical list lengths are strictly below 2^32. No theorem assumes success of a
search, actual execution, an intermediate/final output, or final Freeable
permission. No public helper/global/libc premise is added.

The generic getter/count/wrapper lemmas do have execution or semantic premises
at intermediate composition boundaries. The public proofs discharge them:

- Getter32 concrete fn_vars/params/temps/return/body and field-offset checks
  are reflexive/computational facts about the actual generated function.
- `eval_bitcoin_getter32_layout`, the version layout and the index layout
  allocate the fresh 16-byte source local, derive its loadbytes/storebytes copy,
  preserve original loads and permissions and derive write32 from initial
  writable output capacity. Preserved Freeable permissions derive the final
  Mem.free; free_list is checked in the real function-call rule.
- The script-CMR proof constructs HMid inside the proof from its initial array,
  pointer and separation facts. `write32s_run_layout` derives each Mint32 load
  and write32 call and preserves the remaining input words; the run is not a
  public assumption. `eval_write32s_from_run` follows the actual pointer/count
  loop, including the zero-counter break. The wrapper then derives its return
  and local cleanup.
- Symbol/find_funct facts resolve write32/write32s in the actual Bitcoin global
  environment. LSBclear/LSBkeep have directly proved execution for any global
  environment; the Bitcoin adapters resolve their real functions. Syntax
  similarity alone is not used as an assumed execution transport.
- Writers handle both word-boundary crossing and noncrossing cases. No output
  cursor alignment beyond the common frame contract narrows these theorems.

## Word/domain and canonical-port review

Coq Version uses a signed Int representative, whereas canonical Haskell uses
Word32. This is not a sign restriction: `bitcoin_version_word_signed_unsigned`
proves equality after Word32 encoding for every Int, and the C physical field
is related to the logical unsigned value. High-bit and maximum versions remain
in the domain. LockTime preserves all Word32 values. Logical current index is
bounded by the valid canonical environment and the uint32 input count, so its
Word32 representation matches Haskell's envIx; no extra jet-specific index
restriction is introduced. Haskell `primEnv` checks the same valid-index
condition (`Primitive.hs:99–106`).

For counts, `first_fail_body`, `first_fail_program`, `for_while_program` and
`assertion_cmr_fail0` were compared with the actual
`Haskell/Core/Simplicity/Programs/Word.hs:358–369` definitions. The op/pair/case
routing returns the index on Left, continues on Right, propagates None and
uses the canonical assertl at loop completion. Word32 is recursion depth 5;
SingleV tries false then true and DoubleV nests high/low counters in order.
The semantic list-count bridge proves every smaller index returns Right and
index length returns Left, using ordered-search lemmas and nth_error. It does
not substitute an unproved numeric count formula for the canonical term.

`sigTxInBounds`/`sigTxOutBounds` match uint32 counts in the original raw C API
(`C/include/simplicity/bitcoin/env.h:53–54`). Nonempty inputs follow from a
valid canonical current index; zero outputs and count UINT32_MAX are allowed.
These bounds do not assert representability of arbitrary Haskell vectors beyond
this C API. Numeric payloads cannot change lookup success: signed Word64
representatives encode all original Word64 amounts, as reviewed in the earlier
value-domain correction. No monetary bound or no-overflow premise is used.

For script CMR, canonical `integerHash256` interprets bytes big endian
(`Haskell/Core/Simplicity/Digest.hs:44–57,80–81`). Coq `from_hash256` orders its
eight unsigned Word32 registers from high to low (`Simplicity/Word.v:248–252`).
The hash length field makes its fallback branch unreachable. The actual
write32s emits these same eight words in order; `encode_from_hash256` proves
this equals canonical Word256 encoding. There is no hash computation in this
jet: the script CMR is an environment field in the canonical primitive too.

Initial representation predicates contain loads and logical-field
correspondence, not jet calls, output frames or final memories. The common
frame/address/nonwrap/writable-capacity contracts remain explicit. Script CMR
also requires its eight source words separated from the bytes modified by the
output; this protects later reads during the multiword write. These are local
memory contracts, not a claim about every arbitrary placement/aliasing of C
objects. Their general admissibility remains part of the shared-contract review.

C `env.c:96–100` copies the raw counts/version/locktime and `env.c:233` converts
scriptCMR bytes to the stored midstate. This source inspection explains the
representations; **no end-to-end constructor correctness proof is claimed**.
The valid-index API precondition is documented in `txEnv.h:100–104`.

## Verification evidence and limits

`/tmp/jet-inherited-bitcoin-getters-source-review.json` records source hashes
and equality with the compiled review worktree. The public contracts and their
execution/canonical support are unchanged from the accepted proof inputs.
This round made no proof/manifests/snapshot/C/Haskell edits.

The isolated file
`/Users/brenorb/.codex/jet-proof-scratch/original-c/review_inherited_bitcoin_getters.v`
contains nine closed diagnostics plus one general search-domain lemma. It
checks literal firstFail at zero and UINT32_MAX without enumerating billions
of counters, empty/two-item lists, all-success assertion failure, high-bit/max
version encoding, maximum locktime and asymmetric big-endian hash ordering.
It also Check/Print Assumptions the six actual registered public theorems.
All six retain the same six inherited Coq/CompCert assumptions, with no extra
memcpy/global/helper premise. The first elaboration attempt needed an explicit
Datatypes.unit because imported combinator unit shadowed the type; the corrected
complete file compiled successfully.

- Complete-file compilation: `/tmp/jet-inherited-bitcoin-getters-review-compile.log`,
  exit 0 (session 44545 terminal).
- Separate kernel check: `/tmp/jet-inherited-bitcoin-getters-review-kernel.log`,
  `getters_review_kernel_exit_status=0` (session 65156 terminal), with no
  type-in-type, unsafe fixpoints or assumed positivity.

The diagnostics supplement the source/definition/precondition/conclusion review;
they do not replace the universal public proofs and add no coverage. Constructor
establishment and the global inherited review remain open. The matrix now has
18 reviewed local contracts, 36 prior family reviews, one prior complete chain,
292 registered rows needing remaining evidence cross-reference, and 186 missing
final registrations. The registered inventory remains 347/533, including 104
explicit libc-conditional entries.
