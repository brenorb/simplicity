# Continue from the checked whole reduce512 function

Update: the whole original scalar_mul caller **body** for r=a, its fresh
uninitialized product buffer, both actual helper calls, exact modulo output
and framing are now checked in `../scalar-mul-caller/CONTINUATION.md`.
Caller function entry/allocation/free and square's a=b alias remain open.
Use that continuation next; the historical composition TODOs below are
partially superseded. This adds no public jet coverage.

Last verified declaration:
`MulC.jet_secp_reduce512_function_numeric.eval_reduce512_numeric_owned_loads`.
All eight archived modules compile; fresh build, drivers and independent
kernel check exited zero. No unfinished goal remains in this archive.

## Next end-to-end dependency chain

1. Compose the checked original `scalar_mul_512` product and this full reduction
   into the actual `secp256k1_scalar_mul` caller. Inspect its generated body,
   local 64-byte array allocation, arguments and cleanup before decomposition.
   Prove that product's initialized output is the reduction's actual input in
   the current memory. Do not assume a call, output, load, allocation or free.
2. Handle square through the actual source body/call, reusing multiplication
   only where actual linkage and aliasing/region contracts permit it.
3. Compose public jet readers, scalar normalization, caller, writers and
   cleanup under general evaluator-frame contracts.
4. Close the public result against **literal canonical Simplicity**
   multiplication/square, retaining original raw inputs. Normalized-product
   modulo-order equalities are internal adapters, not substitute public specs.
   The immutable dependency base contains
   `C.jet_secp_canonical_scalar_negate`, including
   `canonical_scalar_multiply` and literal normalization support.
5. Audit full theorem types, definitions and exact dependencies, verify each
   new registered closure, then reconcile main coverage separately. This helper
   alone adds zero public jets.

## Verified interfaces and reuse

- `eval_scalar_mul512_owned_product`: actual eight-limb product helper.
- `eval_reduce512_numeric_owned_loads`: complete original reduction call, final
  memory loads and original 512-bit integer modulo canonical order. It assumes
  two legitimately owned entry regions, not executability or output facts.
- `revalue_u64` and representation lemmas compress initialized symbolic cells
  into exact typed machine leaves **without changing rho, memory, offsets,
  permissions or ownership**. Never forget initialized output before a reader.
- The final overflow argument is the actual ulong addition and narrowing cast,
  not an assumed Boolean. Carry bounds and the modulo identity are discharged
  from earlier checked folds; no `c<=1` or `v<2N` premise is left on the call.
- The whole-body proof reconstructs the original source spine and preserves
  real input/output/local ownership throughout. It does not use the earlier
  monolithic symbolic numeric experiment.

## Diagnoses that avoid repeated dead ends

- A polymorphic `In_nth` bound may print identically to the desired bound but
  contain `length (positive * Z)` instead of `length (block * Z)`. Use
  `Set Printing All` to inspect the mismatch. The checked fix is
  `change (r < length beta)%nat in Hr` before arithmetic rewriting. Two
  failed tactics are a reason to inspect, not expand the search timeout.
- For an owned-prefix length, use `firstn_length`, the proved region length
  and `app_length`; expose `Nat.min 2 (2 + length regsN)` by `change`.
  Broad `cbn [length]` does not automatically unfold the region definition.
- Frame allocation/body/free with
  `Mem.valid_block m b /\\ ~ foot beta original_shapes b ofs`, where `m`
  is the **original caller memory**. Fresh locals are not valid there but are
  valid in the body's memory. Plain outside-foot preservation is insufficient
  as an intermediate predicate. Finally weaken with `lframe_implies`.
- Normalize only a specific nested map/nth_error or foot shape by `change`;
  do not unfold the generated program or symbolic machine arithmetic.
- Literal `Require Import` of a consumer does not re-export every name in its
  dependencies. Import the defining module explicitly.
- The final carry-one case cannot use a canonical reduce theorem that requires
  its flag equal the overflow comparison: actual carry contributes one although
  stored limbs are below the order. The checked `final_output_weighted` and
  `final_modulo_identity` cover the actual combined flag and casts.

## Working discipline and coordination

Use the pinned toolchain and dedicated narrow scratch load path described in
README. Default tactic timeout is ten seconds, speculative coqtop is bounded
at 60 seconds, explicit module processes at 150, independent kernel at 300.
Poll the returned session instead of starting concurrent compilation. Freeze
proof sources/manifests/C/specifications while an audit is running.

Preserve the pending scalar-add candidate and unrelated staged/unstaged
SHA/range/field-negate work. Main coverage is 351/533, not the isolated359.
Claude reserves shared memcpy/SHA/constructibility and Elements foundation,
transport and getters; this scalar work does not overlap. Do not mutate its
worktree or registries. Frequent signed atomic local commits only; no pushes.
