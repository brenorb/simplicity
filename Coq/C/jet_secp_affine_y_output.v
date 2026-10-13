(** Actual affine Y calls retain X, flag and whole-object ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_field_negate_storage.
Require Import C.jet_secp_owned_field_slice C.jet_secp_owned_field_transport.
Require Import C.jet_secp_affine_weak_exec C.jet_secp_affine_y_arithmetic.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem affine_y_arithmetic_output m b value xlimbs flag :
  0 <= value < 2^256 -> (length xlimbs <= 5)%nat ->
  fe_at m b 0 xlimbs -> fe_at m b 40 (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 88 Cur Freeable -> Mem.load Mint32 m b 80 = Some (Vint flag) ->
  exists mw mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
      [Vptr b (Ptrofs.repr 40)] E0 mw Vundef /\
    Clight2.eval_funcall secp_ge mw (Internal f_secp256k1_fe_negate)
      [Vptr b (Ptrofs.repr 40);Vptr b (Ptrofs.repr 40);Vint Int.one] E0 mf Vundef /\
    fe_at mf b 0 xlimbs /\
    fe_at mf b 40 (negate_values (write_fe_rho value 0)) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\
    Mem.load Mint32 mf b 80 = Some (Vint flag) /\
    lframe (fun bx pos => ~ foot [(b,0)] (map rshape (affine_initial_regs AffineY)) bx pos) m mf.
Proof.
  intros HV HLen HX HY HFree HFlag.
  destruct (affine_y_arithmetic_calls m b value HV HY HFree)
    as (mw & mf & HW & HN & HYF & HFF & HF).
  assert (HValid : Mem.valid_block m b).
  { eapply Mem.perm_valid_block; apply (HFree 0); lia. }
  assert (HXFinal : fe_at mf b 0 xlimbs).
  { eapply (owned_field_load_transport 0 88 m mf b xlimbs);
      [lia|exact HLen|exact HX|exact HFF|].
    intros i Hi; apply (proj1 HF); [exact HValid|].
    intros pos HPos HFoot.
    change (foot [(b,0)] (map rshape (owned_field_slice 40 88)) b pos) in HFoot.
    destruct (owned_field_slice_foot_bounds 40 88 b b pos HFoot) as [_ HRange].
    change (size_chunk Mint64) with 8 in HPos; lia. }
  assert (HFlagFinal : Mem.load Mint32 mf b 80 = Some (Vint flag)).
  { rewrite (proj1 HF Mint32 b 80 HValid); [exact HFlag|].
    intros pos HPos HFoot.
    change (foot [(b,0)] (map rshape (owned_field_slice 40 88)) b pos) in HFoot.
    destruct (owned_field_slice_foot_bounds 40 88 b b pos HFoot) as [_ HRange].
    change (size_chunk Mint32) with 4 in HPos; lia. }
  exists mw,mf; split; [exact HW|]; split; [exact HN|]; split; [exact HXFinal|].
  split; [exact HYF|]; split; [exact HFF|]; split; assumption.
Qed.
Timeout 60 Print Assumptions affine_y_arithmetic_output.
