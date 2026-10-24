(** Recover the complete modulus-block frame from readonly preservation of
    the SAME constructed inverse execution. CTZ remains explicit; no generic
    external-call properties or determinism are imported to close the gap. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word C.jet_toZ C.jet_predicate_spec.
Require Import C.extraMath C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_closed_helpers
 C.jet_clight_internal_preserve C.jet_clight_readonly_frame
 C.jet_secp_modinfo_scalar_initialized C.jet_secp_modinfo_scalar_global C.jet_secp_scalar_inverse_caller
 C.jet_secp_scalar_inverse_var C.jet_secp_scalar_invert_literal C.jet_secp_scalar_add_initial
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_overflow_numeric C.jet_secp_canonical_scalar.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge scalar_inv_modinfo_block.

Theorem modinfo_scalar_preserved_frame m mf : modinfo_scalar_initialized m ->
 readonly_preserved m mf -> modinfo_scalar_global_rep mf ->
 modinfo_scalar_initialized mf /\ lframe(fun b _=>b=scalar_inv_modinfo_block) m mf.
Proof.
 intros(Global & Bounds) Preserved OutGlobal.
 pose proof(proj1 Global) as Valid;pose proof(proj1(proj2 OutGlobal)) as Read.
 split.
 - split;[exact OutGlobal|].
   eapply readonly_bounds_transport;[exact Valid|exact Bounds|exact(proj1 Preserved)|exact Read].
 - apply(readonly_region_lframe m mf scalar_inv_modinfo_block 0 48 Valid Bounds Read).
   apply secp_preserved_readback;exact Preserved.
Qed.

Theorem eval_scalar_inverse_var_initialized w m bd bx :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 modinfo_scalar_initialized m -> scalar_at m bx 0 (scalar_add_values w 0) ->
 Mem.range_perm m bx 0 32 Cur Freeable -> Mem.range_perm m bd 0 32 Cur Freeable ->
 0<=scalar_limb_value w<canonical_group_order -> exists result mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_inverse_var)
  [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf bd 0 (scalar_add_values result 0) /\
 scalar_limb_value result=literal_scalar_invert_numeric(scalar_limb_value w) /\
 (forall input:Ty.tySem(Word 8),scalar_limb_value w=@toZ (WordToZ 8) input mod canonical_group_order ->
  @fromZ (WordToZ 8) (scalar_limb_value result)=@literal_scalar_invert Alg.CoreFunSem input) /\
 Mem.range_perm mf bd 0 32 Cur Freeable /\ modinfo_scalar_initialized mf /\
 lframe(fun b _=>b<>bd /\ b<>bx) m mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Initialized Input FX FD Range.
 destruct(eval_scalar_inverse_var w m bd bx CountCall (modinfo_scalar_initialized_state m Initialized) Input FX FD Range)
  as(result & mf & Call & Output & Numeric & Literal & Free & Global & Frame & Preserved).
 destruct(modinfo_scalar_preserved_frame m mf Initialized Preserved Global) as(Ready & GlobalFrame).
 assert(Whole:lframe(fun b _=>b<>bd /\ b<>bx) m mf).
 { eapply lframe_add_block;[exact Frame|exact GlobalFrame|].
   intros b ofs Mod (D & X);repeat split;assumption. }
 exists result,mf;split;[exact Call|];split;[exact Output|];split;[exact Numeric|];split;[exact Literal|];
 split;[exact Free|];split;[exact Ready|];split;[exact Whole|exact Preserved].
Qed.
