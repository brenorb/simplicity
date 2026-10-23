# Bounded memcpy assumption review

The external `memcpy` premise can be restricted to **1 through 64 bytes for the
jet executions covered by these proofs**. This is not a bound on the evaluator,
the public frame-copy API, every possible `UWORD` configuration, or compiler
introduced copies. All nine source-level `memcpy` sites reachable from the jet
translation units are accounted for below. No production C, generated AST,
canonical specification, compiler option, or jet input contract is changed.

This review starts from `feat/jet-equivalence` at
`a69efe302947f4ec2285c889ec83ff41bc137e94`; implementation branch:
`codex/bounded-memcpy-assumption`. The execution target is the existing
CompCert 3.14 x86-64/Linux LP64, little-endian, `PRODUCTION` configuration, with
64-bit `UWORD` and the pinned glibc 2.36 headers. Headers do not pin the linked
libc implementation. See [JET_TARGET.md](JET_TARGET.md).

## Exact change and logical direction

The only logical change is adding `/\ n <= 64` to the existing size
precondition. The arbitrary-semantics counterpart in
`jet_memcpy_model_consistent.v` receives the same change. The full assumption
before and after is reproduced here.

Before:

```coq
Definition memcpy_model : Prop :=
  forall (ge : Senv.t) m bd od bs os n bytes,
    Mem.valid_block m bs -> Mem.valid_block m bd ->
    Mem.loadbytes m bs (Ptrofs.unsigned os) n = Some bytes ->
    Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od + n) Cur Writable ->
    (bs <> bd \/ Ptrofs.unsigned os + n <= Ptrofs.unsigned od \/
      Ptrofs.unsigned od + n <= Ptrofs.unsigned os) ->
    0 < n <= Int64.max_unsigned ->
    Ptrofs.unsigned os + n <= Ptrofs.max_unsigned + 1 ->
    Ptrofs.unsigned od + n <= Ptrofs.max_unsigned + 1 ->
    exists m', Mem.storebytes m bd (Ptrofs.unsigned od) bytes = Some m' /\
      external_call (EF_external "memcpy" memcpy_sig) ge
        [Vptr bd od; Vptr bs os; Vlong (Int64.repr n)] m E0 (Vptr bd od) m'.
```

After:

```coq
Definition memcpy_model : Prop :=
  forall (ge : Senv.t) m bd od bs os n bytes,
    Mem.valid_block m bs -> Mem.valid_block m bd ->
    Mem.loadbytes m bs (Ptrofs.unsigned os) n = Some bytes ->
    Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od + n) Cur Writable ->
    (bs <> bd \/ Ptrofs.unsigned os + n <= Ptrofs.unsigned od \/
      Ptrofs.unsigned od + n <= Ptrofs.unsigned os) ->
    (0 < n <= Int64.max_unsigned /\ n <= 64) ->
    Ptrofs.unsigned os + n <= Ptrofs.max_unsigned + 1 ->
    Ptrofs.unsigned od + n <= Ptrofs.max_unsigned + 1 ->
    exists m', Mem.storebytes m bd (Ptrofs.unsigned od) bytes = Some m' /\
      external_call (EF_external "memcpy" memcpy_sig) ge
        [Vptr bd od; Vptr bs os; Vlong (Int64.repr n)] m E0 (Vptr bd od) m'.
```

Every other premise and the entire conclusion are unchanged: valid source and
destination blocks, readable source bytes, writable destination range,
non-overlap, non-wrapping addresses, exact `Mem.storebytes` effect, empty trace,
and destination-pointer return. `n` is a byte count (`Z`), not a bit count.
Zero-size behavior remains outside this premise; the relevant C SHA branches
skip zero-size calls.

If `P(n)` is the old precondition and `Q(n)` its conclusion, the old model is
`forall n, P(n) -> Q(n)` and the new one is
`forall n, (P(n) /\ n <= 64) -> Q(n)`. The old model implies the new one.
A theorem requiring the new model therefore assumes less library behavior.
Each application must now prove the additional bound; it cannot be added to a
postcondition or assumed as a new axiom. Both versions of the general SHA helper
lemmas `memcpy_bytes_effect` and `uc_memcpy_exec` acquire bounded-length
preconditions, discharged by the existing SHA block invariants. Public jet
input/output contracts are preserved. The concrete internal byte-loop witnesses
remain valid at their original, more general sizes; they still do not prove the
actual external libc function implements the model.

## Complete relevant source-call inventory

Locations refer to the production C at the base revision, unchanged here.
A maximum describes one actual `memcpy` invocation, not the total bytes processed
by a jet or loop.

| Source call | Third argument | Maximum bytes | Reason and callers |
| --- | --- | ---: | --- |
| `C/frame.c:237`, `copyBitsHelper` | `ROUND_UWORD(n_remaining) * sizeof(UWORD)` | 16 in jets | The ten core macro call sites below request at most 96 bits (the proof helper deliberately supports up to 128). Partial-word handling only decreases the remaining count. With 64-bit, 8-byte words, at most two words are copied. Generic frame API is not bounded by 64 bytes. |
| `C/sha256.h:213`, `sha256_tagged_init` | `sizeof(uint32_t[8])` | 32 | Eight 32-bit words on the target; reached by secp256k1 tagged SHA initialization. |
| `C/sha256.h:230`, `sha256_uchars` loop | `delta` | 64 | Initially `delta = 64 - counter % 64`, hence 1..64; subsequent iterations set it to 64. Applies even to a large input array or large counter. |
| `C/sha256.h:238`, `sha256_uchars` tail | remaining `len` | 63 | The loop has stopped with `len < delta <= 64`; the `if (len)` guard excludes zero. |
| `C/elements/ops.c:87`, `simplicity_generateIssuanceEntropy` | `sizeof(contract->s)` | 32 | `sha256_midstate.s` is `uint32_t[8]`. |
| `C/elements/ops.c:103`, `simplicity_calculateAsset` | `sizeof(entropy->s)` | 32 | Same fixed midstate array. |
| `C/elements/ops.c:119`, `simplicity_calculateToken` | `sizeof(entropy->s)` | 32 | Same fixed midstate array; explicit/confidential wrappers share this call. |
| `C/secp256k1/secp256k1_impl.h:40`, `secp256k1_pubkey_load` | `sizeof(s)` | 64 | The call is guarded by `sizeof(secp256k1_ge_storage) == 64`; the other branch uses field conversions. Reached through x-only key loading and signature verification. |
| `C/secp256k1/secp256k1_impl.h:57`, `secp256k1_pubkey_save` | `sizeof(s)` | 64 | The same guard; reached through x-only key parsing/saving. |

The complete list of **104 instantiated core callers**, with source line,
instantiation line, requested bit count and maximum copy bytes, is in
[jet_memcpy_core_calls.csv](jet_memcpy_core_calls.csv). Its ten macro sites are:

| `C/jets.c` site | Macro family | Instantiations | Maximum requested bits | Maximum bytes |
| --- | --- | ---: | ---: | ---: |
| 308 | `FULL_LEFT_SHIFT_` | 18 | 96 | 16 |
| 335 | `FULL_RIGHT_SHIFT_` | 18 | 96 | 16 |
| 362 | `LEFTMOST_` | 18 | 32 | 8 |
| 390 | `RIGHTMOST_` | 18 | 32 | 8 |
| 433 | `LEFT_PAD_LOW_` | 6 | 32 | 8 |
| 449 | `LEFT_PAD_HIGH_1_` | 4 | 1 | 8 |
| 465 | `LEFT_PAD_HIGH_` | 6 | 32 | 8 |
| 529 | `RIGHT_PAD_LOW_` | 6 | 32 | 8 |
| 545 | `RIGHT_PAD_HIGH_1_` | 4 | 1 | 8 |
| 561 | `RIGHT_PAD_HIGH_` | 6 | 32 | 8 |

The bound is attained: a `sha256_uchars` call with a counter divisible by 64
and at least 64 input bytes copies a full 64-byte block. The guarded public-key
load/save paths also copy exactly 64 bytes.

All SHA callers, including `sha256_uchar`, integer/hash serializers, finalization,
core SHA context additions of up to 512 input bytes, buffer additions, Bitcoin
and Elements hashing and secp256k1 challenges, enter the same `sha256_uchars`
chunking loop. Arbitrary buffer lengths do not increase an individual copy.
The environment builders also use this helper with arbitrary input lengths.

### Generated-code coverage

The five acceptance translation units include the actual frame/core C and,
where applicable, SHA, Bitcoin, Elements and secp256k1 implementations and
headers. Counting actual `Evar _memcpy` calls (not external declarations) gives:

| AST | Calls and containing functions |
| --- | --- |
| `jets.v` | 3: `sha256_uchars` twice; `copyBitsHelper` once |
| `jets_sha.v` | 3: the same three functions/sites |
| `jets_bitcoin.v` | 3: the same three functions/sites |
| `jets_secp.v` | 6: the same three, plus `sha256_tagged_init`, `secp256k1_pubkey_load`, `secp256k1_pubkey_save` |
| `jets_elements.v` | 6: the shared three, plus `simplicity_generateIssuanceEntropy`, `simplicity_calculateAsset`, `simplicity_calculateToken` |
| `jets_bitcoin_env.v` (auxiliary) | 3: the shared three |
| `jets_elements_env.v` (auxiliary) | 6: the shared three plus the three Elements operations |
| `jets_secp256k1.v` (auxiliary) | 5: `sha256_uchars` twice, tagged initialization, public-key load/save |

These are repeated translations of the nine source sites, not additional copy
behaviors. Unused builtin declarations are not calls. Compiler-generated
structure copying and CompCert's defined builtin memory operations are separate
from the abstract plain-libc `EF_external "memcpy"` premise.

### Every direct application of the proof model

| Module / lemma | Copy bytes | New obligation derived from |
| --- | ---: | --- |
| `jet_copyBits_memcpy_helper.memcpy_word_effect` | 8 | Constant size |
| `jet_copyBits_wide_memcpy.memcpy_two_words_effect` | 16 | Constant size |
| `jet_sha_uchars_prep.memcpy_bytes_effect` | `length xs`, 1..64 | Helper length premise; its callers use block-fill length or tail shorter than a block |
| `jet_elements_support_sha_uchars_prep.memcpy_bytes_effect` | `length xs`, 1..64 | Same proof for the Elements global environment |
| `jet_elements_calculate_asset_exec` | 32 | Constant midstate size |
| `jet_elements_env_entropy` | 32 | Constant contract-hash size |

The consistency model is kept definitionally identical to the revised premise;
its existing full-size libc semantics witnesses the restricted contract too.
There are no additional direct model applications elsewhere in the Coq source.
The 64-byte secp calls are included in the C/AST inventory; restricting this
premise does not by itself complete pending signature/curve equivalence proofs.

### Full-tree exclusions and limits

A scan of all `C/**/*.c`, `*.h` and `*.inc` finds 63 plain call sites: the nine
above, 49 in `C/dag.c`, two in `C/type.c`, two in `C/eval.c`, and one in
`C/test.c`. DAG/type calls copy fixed 32-byte hashes but are outside jet
translation units. The test harness is not a production input. The two direct
evaluator copies use rounded input/output bit sizes and can exceed 64 bytes.
The evaluator additionally calls `simplicity_copyBits` with arbitrary type bit
sizes at `C/eval.c:408,444,495`. For example, 576 aligned bits copy nine 8-byte
words, or 72 bytes. This is a counterexample to a whole-library bound, not to
the scoped jet claim. No bound is imposed on those APIs by this proof change.

`UWORD` is configurable; an unusually large type or an ABI with substantial
padding is outside the fixed target. Other native ABIs and compilers require
their own configuration analysis. All repository source and generated-call
sites were accessible. This is not an exhaustive audit of every libc, compiler
release, CPU or deployed binary; no linked production libc was identified or
formally verified. The musl upstream web endpoint could not be retrieved, so
no musl code-path claim is made.

## Research: what becomes easier, and what remains conditional

The bound is justified by the call sizes, independently of any particular
libc implementation. It narrows a future library proof's input domain. The
current Coq development still treats libc as abstract, so it does not execute
fewer libc branches or prove any assembly implementation merely by changing
the premise.

| Primary source reviewed | Supported conclusion | Limitation |
| --- | --- | --- |
| [glibc 2.40 x86-64 vector implementation](https://github.com/bminor/glibc/blob/glibc-2.40/sysdeps/x86_64/multiarch/memmove-vec-unaligned-erms.S) | Short copies use scalar or vector front/end loads and stores. With vector widths 16/32/64, a size at most 64 cannot reach the `more_8x_vec` large-copy path; the unrestricted routine has much more code. | Size subcases remain. ERMS variants also consult a runtime threshold after two vectors. Addresses, instruction semantics and return ABI still matter; this is source inspection, not a machine-code proof. |
| [glibc 2.40 x86-64 IFUNC selector](https://github.com/bminor/glibc/blob/glibc-2.40/sysdeps/x86_64/multiarch/ifunc-memmove.h) | CPU feature/preferences select ERMS, SSE, AVX or AVX-512 implementations. | One reviewed vector routine is not all possible selected implementations. Selection and configuration must be included in any deployed-binary claim. |
| [glibc 2.40 AArch64 SIMD implementation](https://github.com/bminor/glibc/blob/glibc-2.40/sysdeps/aarch64/memcpy.S) | Counts 1..32 use small cases; 33..64 use a bounded medium case. The large-copy loop starts above 128. | 64 is a useful bound, not a universal libc threshold; this architecture is outside the current Clight target. |
| [Arm's own AArch64 implementation](https://github.com/ARM-software/optimized-routines/blob/master/string/aarch64/memcpy.S) | Its 1..64 paths similarly avoid the large pipelined loop; the code handles unaligned accesses. | This is another implementation, not evidence about every Arm runtime or Apple libc. |
| [GCC C dialect options](https://gcc.gnu.org/onlinedocs/gcc/C-Dialect-Options.html) and [library builtins](https://gcc.gnu.org/onlinedocs/gcc/Library-Builtins.html) | GCC recognizes `memcpy` as a builtin and can replace calls with inline copying. `-fno-builtin`/`-fno-builtin-memcpy` control recognition. | Emitted behavior depends on size knowledge, optimization flags, target and compiler version. No compiler flags are changed here. |
| [LLVM memory intrinsics](https://llvm.org/docs/LangRef.html#llvm-memcpy-intrinsic) | LLVM distinguishes memcpy semantics/alignment from the inline form's guarantee of no external calls. | A small source-level copy alone is not a guarantee of one emitted instruction sequence or libc call. |

A concrete implementation check must include every positive size through 64,
all valid source/destination alignments and non-overlap placements, including
objects ending at mapped-page boundaries. The model retains valid memory and
non-wrapping range requirements; a size bound does not authorize over-reading
or overwriting an object. Overlapping head/tail loads within one implementation
are not permission for overlapping source and destination C arguments.

The useful conclusion is therefore: **assume correctness only for the sizes
needed by the jets; some concrete implementations have fewer reachable paths
under that restriction.** It is not a portability proof or a measured reduction
in proof effort for every implementation.

## Changed files

Paths below are relative to `Coq/`.

| Files | Change |
| --- | --- |
| `C/jet_memcpy_model.v`, `C/jet_memcpy_model_consistent.v` | Restrict the model's size premise and its consistency counterpart. |
| `C/jet_sha_uchars_prep.v`, `C/jet_elements_support_sha_uchars_prep.v` | Require 1..64 bytes in the byte-effect helpers. |
| `C/jet_sha_uchars_loop.v`, `C/jet_elements_support_sha_uchars_loop.v` | Bound the copy-call helpers and discharge the bound for each block fill. |
| `C/jet_sha_uchars_exec.v`, `C/jet_elements_support_sha_uchars_exec.v` | Discharge the tail-copy bound from the existing loop exit invariant. |
| `C/jet_elements_make_tapleaf_exec.v`, `C/jet_elements_single_issuance_jet.v` | Limit slow duplicate-block tactics to their existing block-distinctness facts; theorems and timeouts unchanged. |
| `C/snapshots/C.jet_memcpy_model.contracts` | Record the revised model definition. |
| `C/snapshots/C.jet_sha_uchars_prep.contracts`, `C/snapshots/C.jet_elements_support_sha_uchars_prep.contracts` | Record the bounded byte-effect helper types. |
| `C/snapshots/C.jet_sha_uchars_loop.contracts`, `C/snapshots/C.jet_elements_support_sha_uchars_loop.contracts` | Record the bounded copy-call helper types. |
| `C/JET_TARGET.md`, `JET_BUILD.md` | Document the restricted trust boundary and link this review. |
| `C/JET_MEMCPY_BOUND_REVIEW.md`, `C/jet_memcpy_core_calls.csv` | Full rationale, research, exclusions and call inventory. |

## Verification

Validation uses Coq 8.17.1 compiled with OCaml 4.14.4, matching the pinned
CompCert/VST dependency objects, on the macOS/arm64 proof host. The Clight
execution target remains x86-64/Linux.

The existing dependency reader identifies 171 registered jets whose closure
imports `C.jet_memcpy_model`, covering 709 modules. This includes jets whose
final statements have no libc premise. Nine additional manifest modules import
the model outside that closure. All **262 model-importing manifest modules**
are therefore covered by the **718 validation modules** checked here.

| Check | Result |
| --- | --- |
| Production/canonical sources and generation configuration | All 240 pinned files match. |
| Global source and negative tests | All 104 checks pass. |
| Complete affected module build | All 718 modules build. Every direct model application discharges the new size bound. |
| Scoped acceptance for all 171 registered consumers | Pass: 709 modules kernel-checked, assumption records match for 560 modules, contract records match for 587 modules, all five production ASTs regenerate identically, and the audit input fingerprint remains unchanged. |
| Nine additional consumers | All nine build and pass kernel checking, without unsafe kernel features or library axioms outside the existing allowlist. Their available baseline contract and assumption records match (one module has records). |
| Core caller inventory | All 104 CSV rows match their source macro instantiations and call lines; the maximum is 16 bytes on the target. |
| Full unscoped repository acceptance | Stops at the unchanged primality-certificate timeout described below; no full-repository acceptance is claimed. |

The five updated contract snapshots were reviewed. Their changes are the model
bound and the bounded helper preconditions; the printed environment-variable
renaming is alpha-equivalent. Axiom records are unchanged. No new axioms,
admitted proofs, unsafe kernel settings, or weakened output/framing conclusions
are introduced.

Two affected execution proofs needed a small tactic-context cleanup:
`jet_elements_make_tapleaf_exec.v:236` and
`jet_elements_single_issuance_jet.v:491` now retain only the existing block
non-membership facts while proving that freed blocks are distinct. This avoids
searching the accumulated memory context. Their theorem statements and existing
10/15-second proof timeouts are unchanged.

The full `bash Coq/check-jets.sh --accept` attempt passed the global source
checks but failed at the unchanged `jet_secp_field_prime.v:64`: its existing
10-second timeout expires during the closed primality-certificate computation.
An isolated `build-jets.sh --coqc -time C/jet_secp_field_prime.v` reproduces the
failure (10.004 seconds, approximately 9.96 CPU seconds). The file is unchanged
from the base branch and is absent from the complete affected scope. Its timeout
is not relaxed. The scoped command below checks every affected consumer rather
than selecting a sample of passing jets.

Temporary build logs remain outside the repository. The evidence is this change
and the reproducible commands below; no logs or run receipts are committed.

### Reproducing the complete affected scope

From the repository root, with the documented Coq 8.17.1 toolchain and pinned
dependencies, derive the registered set using the existing dependency reader:

```bash
memcpy_jet_set=$(PYTHONDONTWRITEBYTECODE=1 python3 - <<'PYCODE'
import functools, importlib.util
from pathlib import Path
spec = importlib.util.spec_from_file_location("closure", "Coq/jet-closure.py")
closure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(closure)
closure.requires = functools.lru_cache(None)(closure.requires)
rows = (line.split() for line in Path("Coq/C/jet_coverage.tsv").read_text().splitlines()
        if line.strip() and not line.startswith("#"))
print(",".join(jet for jet, root, _ in rows
               if "C.jet_memcpy_model" in closure.closure([root])))
PYCODE
)
bash Coq/check-jets.sh --accept --jets="$memcpy_jet_set"
```

The remaining consumers in `_CoqProject.jets` are these nine modules. Use the
existing build, kernel and snapshot tools for them:

```bash
memcpy_extra_modules=(
  C.jet_bitcoin_sig_all_hash C.jet_frame_executable_registry
  C.jet_memcpy_model_consistent C.jet_sha_startup_env_callers
  C.jet_sha_startup_env_jets C.jet_sha_startup_env_runs
  C.jet_sha_startup_executable C.jet_sha_startup_jets C.jet_sha_startup_runs
)
memcpy_extra_file=$(mktemp)
printf '%s\n' "${memcpy_extra_modules[@]}" > "$memcpy_extra_file"
JET_TARGETS="$(sed 's|[.]|/|g; s|$|.vo|' "$memcpy_extra_file")" \
  bash Coq/build-jets.sh -j4
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o \
  "${memcpy_extra_modules[@]}"
JET_ONLY_MODULES="$memcpy_extra_file" bash Coq/audit-jet-contracts.sh
JET_ONLY_MODULES="$memcpy_extra_file" bash Coq/audit-jet-assumptions.sh
rm "$memcpy_extra_file"
```
