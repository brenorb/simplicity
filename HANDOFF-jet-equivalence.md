# Handoff: prove C jet equivalence to Simplicity

Status: one8 C-to-Simplicity bridge implemented and verified locally;
increment8 specification and conditional Clight composition infrastructure are
also checked. Updated 2026-09-22. The work is local; nothing has been pushed.

## Objective and constraints

Prove that individual jets in the C library implement evaluation of their
Simplicity specifications. The first completed target is
`f_simplicity_one_8`; reuse its direct Clight execution infrastructure for
`simplicity_add_8` and then another simple arithmetic jet such as
`increment_8`.
Mathematical correctness of the Simplicity specifications alone does not satisfy
the task. Work locally; do not push. Do not use `admit`, `Admitted`, new axioms,
unproved helper contracts, or informal comments in place of proofs.

The Coq Proof Engineering skill was applied from
`/Users/brenorb/.codex/skills/coq-proof-engineering/SKILL.md`, including its
Clight-specific guidance. In particular, inspect actual goals and AST shape,
use bounded scalar reduction instead of reducing open memory goals with
`vm_compute`, and distinguish helper/body lemmas from a complete
`eval_funcall_internal` theorem.

The remaining sections are an implementation plan, not claims that the final
jet theorem already exists. Scope searches to the repository and known
dependency directories: the user objected to an earlier search reaching their
Music folder.

The current working copy contains the generated `Coq/C/jets.v` artifact,
`Coq/C/jet_exec.v`, `Coq/C/jet_one8.v`, `Coq/C/jet_write8.v`,
`Coq/C/jet_read8.v`, `Coq/C/jet_increment8.v`, and `Coq/C/jet_spec.v`. The
execution files contain
checked complete-call theorems for the actual generated
`f_simplicity_write8` and `f_simplicity_one_8` functions, plus generalized
`f_simplicity_write8` execution, a fixed-layout complete call for
`f_simplicity_read8`, and conditional `f_simplicity_increment_8` body
composition. The spec file gives
the primitive Simplicity term, its parametricity proof, the decoded output
predicate, and the combined C-to-spec theorem. No desired jet behavior is
assumed as an axiom.

## Verified current state

The following declarations in `Coq/C/jet_exec.v` compile successfully with
CompCert 3.14 and Coq 8.17.1:

* `exec_Sassign_copy` packages the Clight2 `exec_Sassign` constructor.
* `assign_frameItem_copy` packages `Clight.assign_loc_copy` for the generated
  `frameItem` type.
* `eval_frame_edge`, `eval_frame_offset`, `eval_frame_offset_lvalue`,
  `eval_word_lvalue`, `eval_word`, `assign_frame_offset`, and `assign_word`
  evaluate the generated field accesses and stores.
* `call_LSBclear8` and `call_LSBkeep8` resolve calls through the actual global
  environment and actual generated helper functions.
* `write8_prefix_probe` proves the body execution of the generated
  `f_simplicity_write8` path for the fixed call argument `1`, including the
  actual `LSBclear` and `LSBkeep` calls, the word store, and the offset store.
* `eval_write8` packages that body proof with `ClightBigstep.eval_funcall_internal`:
  it includes `function_entry2`, local allocation, normal return, and local
  deallocation. Its hypotheses are concrete CompCert memory/load/store facts,
  not an abstract specification of the helper.
* `Coq/C/jet_one8.v` proves `eval_one8_zero`: the generated
  `f_simplicity_one_8` call returns `Vint (Int.repr 1)`, writes the output
  word to `Int64.repr 1`, and clears the destination cursor, under explicit
  CompCert allocation, alignment, load/store, and free hypotheses.
* `Coq/C/jet_spec.v` defines the canonical primitive one8 term, proves its
  parametricity and functional value, and proves `eval_one8_matches_spec`,
  combining the C execution theorem with the decoded Simplicity postcondition.
* `Coq/C/jet_write8.v` proves the complete actual call theorem
  `eval_write8_x` for an arbitrary C byte argument, under explicit memory and
  actual `LSBclear`/`LSBkeep` execution hypotheses. Its closed-width
  normalization uses bounded scalar reduction only.
* `Coq/C/jet_read8.v` proves `eval_read8`: the generated read8 function's
  complete `Clight2.eval_funcall` at the fixed one-word layout, including the
  actual `LSBkeep` call, load and store facts, and final `tuchar` return cast.
  The layout is the one-past-word edge with source offset 56; the crossing
  branch is discharged by the concrete `8 < 8` test.
* `Coq/C/jet_increment8.v` proves the actual `function_entry2` setup for
  `f_simplicity_increment_8`, composes its generated copy/read/writeBit/write8
  statement tree under explicit helper-execution premises, and records the
  casted-byte environment. `jet_spec.v` defines and proves parametricity of
  `increment8_spec := adder (n := 3) (input, one8)`.

The checked `eval_write8` contract is:

```coq
Lemma eval_write8 : forall (m : mem) (bf bw : block)
    (w c q : int64) (m1 m2 : mem),
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bw 0 (Vlong q) = Some m1 ->
  Mem.load Mint64 m1 bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.store Mint64 m1 bf 8 (Vlong (Int64.repr 0)) = Some m2 ->
  q = Int64.or c
        (Int64.shl (Int64.repr 1)
          (Int64.sub (Int64.repr 8) (Int64.repr 8))) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong w :: Vlong (Int64.repr 8) :: nil) E0 m (Vlong c) ->
  ClightBigstep.Clight2.eval_funcall ge0 m
    (Internal f_simplicity_write8)
    (Vptr bf Ptrofs.zero :: Vint (Int.repr 1) :: nil)
    E0 m2 Vundef.
```

This is a helper theorem used by the completed one8 bridge. The increment8
composition theorem is intentionally conditional: it does not yet prove
`read8` or `writeBit` from a concrete memory layout, and therefore is not yet
the final public C-to-Simplicity equivalence theorem. The remaining extension
is to prove those helper executions and thread the concrete source and
destination frame memories through the call, then connect the decoded output
to `increment8_spec`. The analogous actual-call theorem for
`f_simplicity_add_8` remains future work.

## Simplicity-side target

There is no existing theorem in this repository named `simplicity_add_8` that
already relates the generated C function to a Simplicity term. Define each
bridge explicitly rather than treating a C function name as its specification.
For the completed one8 target, `Coq/C/jet_spec.v` defines the canonical
primitive expression `true >>> left_pad_low word1 word8` by three layers of
the existing `Word.fill`/pair combinators, proves its parametricity, and proves
that its functional semantics is `fromZ 1`.
The relevant existing formal object is in `Coq/Simplicity/Word.v`:

```coq
Word 3 = Word8
adder : Word 3 * Word 3 -> Bit * Word 3
```

The reason for `3` is that `Word n` contains `2^n` bits. The intended semantic
target for `simplicity_add_8` is therefore
`|[adder (n := 3)]| (a,b)`, whose first component is the carry and whose second
component is the eight-bit sum. `Word.v` already proves
`adder_correct 3`, but that lemma is only an integer-value fact; it must not
replace the stronger equality of the complete `Bit * Word 3` result.

Useful existing infrastructure is in `Coq/Simplicity/Alg.v`:

* `CoreFunSem_correct` connects a parametric Core term with its functional
  semantics.
* `CoreSem_initial` connects the monadic/primitive semantics with the pure
  function semantics when the term is parametric.

If the final theorem is stated through the primitive algebra, use the actual
primitive/jet algebra (`Simplicity.Primitive` and, where appropriate,
`Simplicity.Primitive.Bitcoin`) and prove the required parametricity facts. Do
not invent an axiom saying that the C result equals `adder`; the equality must
come from the memory execution proof plus the Simplicity term's semantics.

The C-level result should expose the same shape as the Simplicity result. For a
read frame containing two cells, use a one-UWORD backing word with initial
offset `64 - 16 = 48`; the two `simplicity_read8` calls advance it to `64`. For
a write frame containing nine cells, use a separate backing word with initial
offset `9`; `writeBit` followed by `simplicity_write8` advances it to `0`.
The destination word's first cell must be the carry predicate
`255 - y < x`, and its remaining eight cells must be the truncated sum
`(x + y) mod 256`. Quantify over all `x,y : Word 3` (equivalently all 256 by
256 input values), not just examples.

The final postcondition should state that decoding the destination's nine bits
gives exactly `|[adder (n := 3)]| (a,b)`, while also stating the returned
`Vint Int.one`, source-frame cursor advancement, destination cursor advancement,
and preservation of unrelated memory. A theorem of the form “if the C call
returns, then the result is correct” is too weak unless the call's complete
termination is proved constructively.

For the current prototype, compile the generated AST into a temporary logical
library and then compile the bridge as follows (from the repository root):

```sh
cd Coq/C
env OPAMROOT=/Users/brenorb/.opam-simplicity-root \
  opam exec --switch=simplicity -- coqc -q -o /tmp/jets.vo \
  -R /tmp/simplicity-compcert/lib compcert.lib \
  -R /tmp/simplicity-compcert/common compcert.common \
  -R /tmp/simplicity-compcert/x86_64 compcert.x86_64 \
  -R /tmp/simplicity-compcert/x86 compcert.x86 \
  -R /tmp/simplicity-compcert/cfrontend compcert.cfrontend \
  -R /tmp/simplicity-compcert/export compcert.export \
  -R /tmp/simplicity-compcert/flocq Flocq \
  -R . C jets.v

cd ../..

env OPAMROOT=/Users/brenorb/.opam-simplicity-root \
  opam exec --switch=simplicity -- coqc -q -R /tmp '' \
  -R /tmp/simplicity-compcert/lib compcert.lib \
  -R /tmp/simplicity-compcert/common compcert.common \
  -R /tmp/simplicity-compcert/x86_64 compcert.x86_64 \
  -R /tmp/simplicity-compcert/x86 compcert.x86 \
  -R /tmp/simplicity-compcert/cfrontend compcert.cfrontend \
  -R /tmp/simplicity-compcert/export compcert.export \
  -R /tmp/simplicity-compcert/flocq Flocq Coq/C/jet_exec.v
```

The generated AST was compiled from `Coq/C` so its temporary library name is
`jets`; the bridge therefore imports `jets` directly. When integrating into the
repository build, make the logical name and output location consistent instead
of mixing a stale `.vo` with a different `-R` prefix.

## Correct diagnosis of the previous failure

All relevant public jets pass `frameItem src` by value. The generated normalized
Clight includes:

```coq
Sassign (Evar _src (Tstruct _frameItem noattr))
        (Etempvar _src (Tstruct _frameItem noattr))
```

These are different storage locations despite sharing an identifier. `Evar` is
the function's local memory object; `Etempvar` is the incoming parameter. This
copies the incoming struct into local storage. It is NOT a harmless self-copy
introduced by `(void) src`: `add_8` has the same initialization and uses it.

The attempted funspec supplied `Vundef` for the incoming struct parameter. That
cannot justify this initialization. In this Clight representation the parameter
must carry a pointer to readable storage holding the incoming struct.

VST 2.14 rejects struct parameters and struct assignments. Read-only inspection
found the same guards in VST 2.16 and master. Removing tactic guards did not solve
the missing proof support. Do not repeat that workaround or erase the assignment.

CompCert itself supports struct copies: `Clight.assign_loc_copy` requires source
and destination alignment, an allowed overlap relation, `Mem.loadbytes`, and
`Mem.storebytes`. A freshly allocated local frame is disjoint from the incoming
frame, which should make this case straightforward once memory lemmas exist.

## Recommended route: direct Clight execution proofs

Use `ClightBigstep.Clight2.eval_funcall` for the generated functions, with the
actual program global environment. This uses `function_entry2`, where parameters
are temporaries and local variables are allocated separately. Do not accidentally
use Clight1: its parameter allocation convention differs.

Relevant dependency sources:

- `/tmp/simplicity-compcert/cfrontend/Clight.v`: `assign_loc_copy`,
  `function_entry2_intro`, allocation and parameter binding.
- `/tmp/simplicity-compcert/cfrontend/ClightBigstep.v`: `exec_Sassign`,
  `exec_Scall`, `eval_funcall_internal`, and module `Clight2`.
- `eval_funcall_internal` includes allocation, body execution, return-value
  validation, and freeing local blocks. A proof only of a body suffix omits these
  obligations and is not the final result.
- `Clight2.bigstep_semantics_sound` relates the whole-program big-step semantics
  to `Clight.semantics2`. Inspect its exact statement before claiming a
  per-function small-step corollary; these are different theorem interfaces.

### 1. Establish trustworthy generated input

The prototype generated combined `C/frame.c` and `C/jets.c` by including both in
one translation unit. An AST remains at `/tmp/simplicity-frame-jets.v` (CompCert
3.14, normalized, x86-64, little endian). It contains the real frame helper bodies
as well as public jets, and previously compiled successfully.

Treat this as an exploratory artifact until generation is reproducible. The
prototype used temporary replacement standard headers to avoid Apple SDK parse
failures. Those headers and the temporary translation unit were removed from the
repository. `/tmp/simplicity-compcert-gcc-nostdinc.ini` still references the removed
headers. Merely copying the AST into the repo is not a reproducible workflow.

Prefer supported target headers. If providing minimal target headers is necessary,
document and check every relevant typedef, integer width, macro, assertion setting,
and ABI choice against the intended C build. Do not silently change C semantics.
Record the generation command, compiler version, target, flags, and input files.
Do not hand-edit generated function bodies to make proofs pass.

### 2. Define concrete frame representations

Read `C/frame.h`, `C/frame.c`, and `C/uword.h` before defining memory predicates.
Model the edge pointer, cursor offset, backing words, bounds, alignment, and
permissions. Read and write frames use different cursor conventions.

For the first addition theorem, a practical scope is a single backing UWORD for
the 16 input bits and one backing UWORD for the 9 output bits, with separate
source and destination storage. Quantify over all input values and all unrelated
bits in those words. Clearly state this layout restriction; it is not yet a proof
for every legal frame alignment or aliasing arrangement.

Prove preservation of input memory and unrelated output bits, as well as the
correct destination cursor. Track the caller's source frame separately from the
callee's copied frame. Avoid excessive restrictions such as requiring every
initial output word to be zero.

### 3. Prove helper execution against actual bodies

First build small reusable lemmas for field loads/stores and allocation disjointness.
Then prove the relevant execution paths of:

- `LSBkeep` and `LSBclear` from `C/uword.h`;
- `simplicity_read8` from `C/frame.c`;
- `writeBit` from `C/frame.h`;
- `simplicity_write8` from `C/frame.c`.

Specialized offsets sufficient for the initial layout are acceptable if explicit
in the final theorem. Each call must resolve to the actual function in the global
environment. A helper contract assumed through VST's `Gprog`, an abstract external
call, or a hypothesis asserting the desired execution does not complete this task.
Prove enough memory preservation to compose the helpers without hidden assumptions.

### 4. Compose complete jet invocation

For `simplicity_add_8`:

1. Allocate the local source frame and bind parameters using `function_entry2`.
2. Prove the struct initialization with `exec_Sassign` and `assign_loc_copy`.
3. Execute both `simplicity_read8` calls and the generated casts.
4. Execute the carry expression, `writeBit`, and `simplicity_write8`.
5. Establish return value `Vint Int.one` and free the local frame.

Respect CompCert promotions and casts: the C macro computes the carry as
`1U * UINT8_MAX - y < x` and truncates `1U * x + y` to `uint_fast8_t`.
Check the actual target typedef for that type. Show all shifts, memory accesses,
and divisions used along the path are defined.

### 5. State the result in terms of Simplicity evaluation

CRITICAL: `Word n` has **2^n bits**, not n bits. `Vector X 0 = X` and each successor
doubles the vector. Thus the 8-bit adder is `adder` instantiated at **n = 3**.

`Coq/Simplicity/Word.v` defines `adder` and proves `adder_correct`:

```coq
toZ (|[adder]| (a, b)) = toZ a + toZ b
```

Use that existing lemma plus encoding injectivity/range lemmas as a bridge. The
final postcondition must say the decoded destination bits equal
`|[adder]| (a, b)` for `a b : Word 3`, including the carry bit. An integer-sum
postcondition alone, or another proof of `adder_correct`, is insufficient.
Check notation/imports in `Word.v` and `Alg.v` rather than copying this schematic
notation blindly. Repeat for a second arithmetic jet once infrastructure works.

A useful final theorem shape is: for every valid represented input memory,
there exists a final memory in which a complete call of the actual jet terminates
with empty trace and true return, writes precisely the evaluated Simplicity
result, advances the output cursor correctly, and preserves the stated frame of
unrelated memory. This constructive execution claim prevents a vacuous theorem
that only says 'if the C function returns, its result is correct.' If asserting
uniqueness of every possible execution, establish determinism or prove it separately.

## Existing proof context

Inspect the SHA proof chain rather than assuming a full public-jet theorem already
exists. `Coq/Simplicity/Digest.v` imports VST's SHA functional model and defines
compression through it; that file alone is not a C jet equivalence proof.
The committed `Coq/C/jets_secp256k1.v` is another available generated AST.
Existing VST implementation proofs live in `Coq/C/secp256k1/`, particularly
`verif_int128_impl.v` and `verif_modinv64_impl.v`. Proving only a secp helper would
still need a connection to a public jet and its Simplicity specification.

## Installed local tooling and build notes

- Homebrew installed Rocq, opam, pkgconf, and GCC (available as `gcc-16`).
- Compatible opam root: `/Users/brenorb/.opam-simplicity-root`.
- Switch `simplicity`: OCaml 4.14.1 and Coq 8.17.1.
- Run Coq commands with
  `env OPAMROOT=/Users/brenorb/.opam-simplicity-root opam exec --switch=simplicity -- ...`.
- CompCert 3.14: `/tmp/simplicity-compcert`; `clightgen` exists there.
  Configured for `x86_64-linux` with `-clightgen` and prefix
  `/tmp/simplicity-compcert-install`. Coq libraries and generator built; the native
  x86 runtime assembly build failed on this ARM Mac. Do not claim a native C
  executable build succeeded.
- VST 2.14: `/tmp/simplicity-vst`, built against the above CompCert. Its `sha`
  target was also built. Direct Clight proofs should avoid VST imports except
  where existing Simplicity dependencies require them.
- Additional read-only inspection clones: `/tmp/simplicity-vst216` and
  `/tmp/simplicity-vst-master`. Their presence does not mean they are built.
- Temporary paths may disappear. Check them before use.

CompCert load paths used previously (`-R directory logical-prefix`):

```text
/tmp/simplicity-compcert/lib         compcert.lib
/tmp/simplicity-compcert/common      compcert.common
/tmp/simplicity-compcert/x86_64      compcert.x86_64
/tmp/simplicity-compcert/x86         compcert.x86
/tmp/simplicity-compcert/cfrontend   compcert.cfrontend
/tmp/simplicity-compcert/export      compcert.export
/tmp/simplicity-compcert/flocq       Flocq
```

VST load paths used `-Q /tmp/simplicity-vst/<dir> VST.<dir>` for `msl`, `sepcomp`,
`veric`, `zlist`, `floyd`, `progs64`, `concurrency`, and `atomics`, plus
`-Q /tmp/simplicity-vst/sha sha`. In `Coq/`, add `-Q Simplicity Simplicity -R C C`.
Generate a makefile from `_CoqProject` with needed dependency mappings and compile
targeted proof files. The previous full project build had missing `divsteps`
dependencies; targeted Simplicity Word dependencies compiled. Report targeted
success accurately rather than claiming the entire project passes.

## Completion checks

- Compile every new theorem and its transitive new dependencies with Coq.
- Inspect `Print Assumptions` on final theorems; explain inherited assumptions
  and ensure no desired implementation behavior was introduced as an axiom.
- Check generated-source provenance and the exact function/global environment
  named by each theorem.
- Verify all 256 x 256 inputs are quantified over, carry and truncation included;
  spot examples such as 0+0 and 255+1 can supplement but cannot replace the proof.
- State layout, aliasing, target, and assertion-mode restrictions explicitly.
- Provide local files, repeatable generation/build instructions, and a short
  explanation of what the final theorem proves. Leave no aborted exploration
  presented as finished work, and do not push.
