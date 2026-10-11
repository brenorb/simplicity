# Memcpy-linked jet proofs

Branch `claude/shared-obligations` (forked from `a8685146`). Nothing here is
registered in the shared coverage/manifest files; integration is left to the
owner of `feat/jet-equivalence`.

## What is proved, and for which program

The accepted proofs state the memcpy-dependent jets as
`memcpy_model -> contract` for the generated program `Coq/C/jets.v` (and
`jets_sha.v`), in which `memcpy` is an *external* declaration whose semantics
is CompCert's abstract parameter `external_functions_sem`. That premise cannot
be proved for the unchanged program: nothing in Coq determines what an
external function does. **This work does not discharge it for the unchanged
program and does not claim to.**

What it proves instead:

1. `Coq/C/jet_memcpy_exact.v` — a concrete libc-ABI `memcpy`
   (`jet_memcpy_exact.c`, translated by clightgen to `memcpy_exact.v`) run as
   an *internal* Clight function in any global environment returns the
   destination pointer with an empty trace and leaves exactly
   `Mem.storebytes` of the loaded source bytes, under the premises of
   `memcpy_model` (theorem `eval_memcpy_exact`). It copies each byte with
   CompCert's defined block move `EF_memcpy 1 1`, so it is exact for
   arbitrary memory values.
2. `Coq/C/jet_memcpy_impl.v` — the plain C byte loop `d[i] = s[i]`
   (`jet_memcpy_impl.c`) satisfies the same conclusion when the source range
   holds initialized data bytes (`eval_memcpy_impl`). This premise is a real
   requirement of that code under Clight (an `unsigned char` load of an
   undefined byte or pointer fragment is `Vundef`, rejected by the
   assignment cast), and the jet contracts do not provide it at the
   memory-value level, so this variant is *not* the one linked below.
3. `linked/C/jet_linked_program.v` — the *linked program* (the accepted
   `jets.v` with the external declaration of `memcpy` replaced, in place, by
   the internal definition of item 1) is CompCert's link of the accepted
   program with the memcpy translation unit: `linked_ast_is_compcert_link`
   (generic program linker, closed under the global context) and
   `linked_program_is_compcert_link` (Clight program linker including
   composites; inherits `Axioms.proof_irr` from CompCert's own definition of
   `link_program`, and is the only statement here that does).
4. `linked/C/jet_memcpy_model.v` — in the linked program `memcpy_model`
   (same premises and memory conclusion; the call is the big-step execution
   of the linked definition) is a theorem, `memcpy_model_holds`.
5. `linked/C/jet_linked_memcpy_jets.v` and `linked/C/*_linked.v` — every
   accepted `X : memcpy_model -> S` yields `X_linked : S` **for the linked
   program**. `S` is copied verbatim from the accepted source by the
   generators, and the proof is `X memcpy_model_holds`, where `X` is the
   accepted proof script compiled unchanged against the linked program.

So the boundary is: the contracts hold unconditionally for the jets C code
linked (by CompCert's linker) with the reference `memcpy` of item 1. For a
build linked against another libc, the remaining assumption is that its
`memcpy` behaves, on the calls the jets make, like that reference definition;
this is outside Coq and is not claimed.

## Consistency of the premise for the unchanged program

Independently of linking, `C/jet_memcpy_model_consistent.v` shows that
`memcpy_model` — a statement about CompCert's abstract parameter
`external_functions_sem "memcpy"` — is consistent with CompCert's constraint
`external_functions_properties`: an assignment of semantics to every external
function exists that satisfies `extcall_properties` everywhere and makes the
statement of `memcpy_model` true (`memcpy_model_consistent`, closed under
the global context). The accepted conditional theorems are therefore not
vacuous because of an inconsistent premise. It remains a premise: nothing
identifies CompCert's parameter with the libc contract.

## How the linked proofs are built

`bash Coq/build-linked.sh [-jN]` creates `Coq/linked/tree/` (ignored by git):
symbolic links to every accepted `Coq/C/*.v` under the same logical names,
except

- `jets.v`, `jets_sha.v`: produced by `linked/gen-jets.py` (three checked
  edits: declare `_dest`, insert `f_memcpy`, replace the external entry at
  the same position of the definition list, so block numbering is unchanged);
- `jet_memcpy_model.v`: `linked/C/jet_memcpy_model.v`;
- `jet_copyBits_memcpy_{exec,helper}.v`, `jet_copyBits_wide_memcpy.v`,
  `jet_sha_uchars_{prep,loop}.v`: derived by `linked/patch-consumers.py`
  (the external-call premise/conclusion becomes `memcpy_call`, the call node
  is that derivation; 15 changed lines in total, each rule count-checked);
- `jets_unlinked.v`: the accepted `jets.v`, for the linking theorem.

All other modules, including every jet proof, are the accepted sources.
`linked/gen-linked-theorems.py` and `linked/gen-linked-sha-theorems.py`
regenerate the `_linked` theorem modules and fail if the set or shape of
conditional theorems changes.

## Receipts

See `linked/RECEIPTS.md`.
