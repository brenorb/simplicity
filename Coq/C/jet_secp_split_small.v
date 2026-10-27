(** The actual complete split_lambda call stores the residues of two proved
    small signed integers. Connecting these values to the literal Simplicity
    signed-half term remains separate; this is not a public jet registration. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_secp_linkage C.jets_secp C.jet_sx_mem C.jet_secp_canonical_scalar
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_split_constants C.jet_secp_split_function C.jet_secp_split_signed_bounds
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_scalar_split_lambda_small (k:Ty.tySem (Word 8)) m bk br1 br2 :
 0<= @toZ (WordToZ 8) k<canonical_group_order -> split_constants_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m br1 0 32 Cur Freeable ->
 Mem.range_perm m br2 0 32 Cur Freeable -> NoDup [bk;br1;br2] ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_split_lambda)
 [Vptr br1 Ptrofs.zero;Vptr br2 Ptrofs.zero;Vptr bk Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of (split_signed_first (@toZ (WordToZ 8) k) mod canonical_group_order))) /\
 scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of (split_signed_second (@toZ (WordToZ 8) k) mod canonical_group_order))) /\
 (-2^128<split_signed_first (@toZ (WordToZ 8) k)<2^128) /\
 (-2^128<split_signed_second (@toZ (WordToZ 8) k)<2^128) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) /\
 Mem.range_perm mf br1 0 32 Cur Freeable /\ Mem.range_perm mf br2 0 32 Cur Freeable /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ split_constants_ready mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (split_function_frame bk br1 br2) m mf.
Proof.
 intros Range Ready Input FK FR1 FR2 Separate.
 destruct (eval_scalar_split_lambda k m bk br1 br2 Range Ready Input FK FR1 FR2 Separate)
  as (mf & Call & First & Second & Rest).
 rewrite split_first_signed in First;rewrite split_second_signed in Second.
 destruct (split_signed_bounds _ Range) as [Small1 Small2].
 exists mf;split;[exact Call|];split;[exact First|];split;[exact Second|];
 split;[exact Small1|];split;[exact Small2|exact Rest].
Qed.
