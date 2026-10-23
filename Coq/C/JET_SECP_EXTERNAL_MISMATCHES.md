# Secp external-call semantics gaps

This is a proof-model limitation, **not a demonstrated mismatch between the
production C and the fixed Simplicity specification**. No implementation,
specification, API contract, generated AST or generation setting is changed.
The affected jets remain unresolved; these diagnostics add no coverage.

## Inversion: counting trailing zeroes is an abstract external call

Directly affected: `simplicity_fe_invert` and `simplicity_scalar_invert`.
Their C helpers call `secp256k1_modinv64_var`, whose divstep batches call
`secp256k1_ctz64_var`. Callers needing those inversions inherit this boundary;
this is not an exhaustive downstream call-graph claim.

For a nonzero 64-bit word, the needed helper contract is the number of trailing
zero bits, with unchanged memory and an empty trace. For example, argument 1
must return 0. The frozen production translation does not use the software
de Bruijn fallback: its unsigned-long-width guard is true and selects
`__builtin_ctzl`. The generated declaration is `EF_builtin "__builtin_ctzl"`
with signature `[Tlong] -> Tint`.

In the pinned CompCert 3.14, lookup for that name/signature returns `None`.
The alternate `__builtin_ctzll` also returns `None`. `builtin_or_external_sem`
therefore dispatches to the parameter `Events.external_functions_sem`, not to
a known counting function. The generic external-call properties specify no
ctz result and do not even guarantee that a call can return.

`jet_secp_ctz_semantics_gap.v` provides formal evidence for the actual guard,
callee and external declaration, both failed builtin lookups, and the dispatch
equation. Its `ctz_generic_properties_insufficient` is a closed countermodel
argument: the empty call relation satisfies `extcall_properties` but cannot
supply a result even for argument 1. This does **not** assign that relation to
CompCert's actual abstract parameter, demonstrate a stuck execution under a
chosen concrete library, or demonstrate an incorrect native C result. It
establishes that those generic properties alone cannot discharge the required
execution premise. The countermodel is diagnostic only, not a substitute
implementation or a semantics used by a registered jet proof.

`jet_secp_ctz_external_call.v` additionally proves the dependency through the
actual helper's execution, not merely its syntax. `eval_ctz64_requires_external`
extracts an `external_functions_sem "__builtin_ctzl"` call from any completed
execution of the original `secp256k1_ctz64_var`, with the same argument and
initial memory. It does not identify the extracted call's trace, result or
final memory with those of the complete helper. Conversely,
`eval_ctz64_from_external` constructs the complete original helper execution
when given an empty-trace external call returning an integer. That premise
remains explicit and unresolved; it does not assert a counting law, memory
preservation, or that such a call exists. These results use six inherited
assumptions, without the external-call determinism axioms. They do not yet
extract this call from a complete divstep batch or public inversion jet.

## Generation: wNAF also calls external memset

The original `secp256k1_ecmult_wnaf` calls `memset` to initialize its digit
array. The generated declaration is `EF_external "memset"`, with signature
`[Tlong; Tint; Tlong] -> Tlong`. The same diagnostic module formally checks
the declaration and the call in the actual helper body. Its mere presence
does not prove the zeroing behavior or the validity of a particular call's
arguments. `generate` and other ecmult callers still need a discharged
external-library boundary in addition to their arithmetic and execution
proofs. The scalar-splitting helper proof does not rely on memset or ctz.

`jet_secp_wnaf_entry15.wnaf_entry15_owned_output` additionally derives the
actual function entry and all eight preparation statements for the
generator's len=129/window=15 calls. It evaluates the real call arguments to
`(destination, 0, 516)`, preserves the destination's 516 Freeable bytes,
allocates the actual distinct 32-byte scalar local and preserves all old
memory up to the call. It assumes no zeroing or external-call execution.
This is positive execution evidence for entry/setup and valid destination
capacity, not a completed memset or wNAF call, nor an extraction theorem
from every completed public generate call. In particular, it supplies no
reason to identify the abstract external parameter with a concrete libc.
Build/check it with the commands below, substituting the target/module
`C/jet_secp_wnaf_entry15.vo` / `C.jet_secp_wnaf_entry15`.

## Internal normalization dependency

`jet_secp_modinv_normalize62_exec.eval_norm62_from_storage` derives the
complete original `secp256k1_modinv64_normalize_62` call from five owned
signed62 words and five read-only modulus words. It returns the exact
machine-word result, output ownership, unchanged modulus words/readability,
and framing outside the two 40-byte regions. The source need not be writable
or have nonnegative limbs. In particular, this interface does not exclude
the actual sparse field modulus's negative low limb.

This C-level dependency compiles and passes recursive kernel checking with
the same six inherited execution assumptions and no external-library model.
Its symbolic-run, return, output-shape and word-denotation certificates are
closed. It adds no registered jet: modular-inverse batch/loop composition
and ctz linkage are still required.
It is not a proof about the mathematical correctness of a jet specification
and does not repair or bypass the external-call boundary above.

`jet_secp_modinv_normalize62_global.eval_field_norm62_with_global` specializes
the call to the actual field-modulus global, reusing `modinfo_fe_limb` rather
than another modulus definition. It derives the call, exact output and
retained private ownership, and preserves the complete
`modinfo_fe_global_rep`: all 48 readable bytes and all six words, including
the untouched inverse coefficient at +40. Startup readiness is the existing
predicate established by `modinfo_fe_global_initializes`; neither an
initialized result nor a helper execution is assumed. This is still a
normalization dependency, not the public inverse jet.

`jet_secp_modinv_normalize62_numeric.norm62_field_machine_numeric` now proves
the numeric bridge for that exact machine-word result. For the helper's
internal signed-limb bounds and an aggregate input in `(-2*p,p)`, it returns
canonical nonnegative signed62 limbs whose value is `(sign*input) mod p`.
Here `sign` is -1 for a negative C sign argument and +1 otherwise. The proof
uses the actual sparse modulus, accounts for both conditional additions,
conditional bitwise negation and both signed carry passes, and proves that
the intermediate word additions do not overflow. Its numeric lemmas are
closed; `eval_field_norm62_numeric` composes them with the original C call
and retains ownership, all global metadata and byte-range framing, with the
same six inherited execution assumptions and no libc premise.

These are derived internal helper conditions, not new restrictions on
public jet inputs. The inverse loop must establish them. Neither a public
inversion equivalence nor additional jet coverage is claimed. Reproduce:

```sh
JET_TARGETS=C/jet_secp_modinv_normalize62_exec.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_normalize62_exec
JET_TARGETS=C/jet_secp_modinv_normalize62_global.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_normalize62_global
JET_TARGETS=C/jet_secp_modinv_normalize62_numeric.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_normalize62_numeric
```

## Reproduction and limits

With the pinned dependencies from `Coq/JET_BUILD.md`:

```sh
JET_TARGETS=C/jet_secp_ctz_semantics_gap.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_ctz_semantics_gap
JET_TARGETS=C/jet_secp_ctz_external_call.vo bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_ctz_external_call
```

Inspect the named statements or the reviewed snapshots for their exact scope.
The lookup/countermodel evidence is formal. No native reproducer or native
wrong-result observation is claimed. In particular, this report does not
claim that a zero word is passed to a compiler builtin with a nonzero-input
contract; the divstep code adds a sentinel before counting.

The worst established consequence is an unresolved acceptance boundary for
the affected implementation-to-specification proofs, not a demonstrated
runtime failure, consensus discrepancy or exploit. A complete result needs
justified concrete external semantics/linkage; adding an unproved ctz or
memset premise would not meet the goal. Switching the production AST to a
fallback, changing compiler/generation configuration, or changing the target
would require separate explicit approval and is not done here.

