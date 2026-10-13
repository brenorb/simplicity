(** Entire original in-place affine helper: entry, 88-byte copy, calls and return. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_exec C.jet_sx_state C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_field_negate_storage.
Require Import C.jet_secp_owned_field_slice C.jet_secp_owned_field_transport.
Require Import C.jet_secp_affine_weak_exec C.jet_secp_affine_self_copy.
Require Import C.jet_secp_affine_y_output C.jet_secp_affine_y_tail.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_affine_negate_body_output le m b value xlimbs flag :
  le!_r = Some (Vptr b Ptrofs.zero) -> le!_a = Some (Vptr b Ptrofs.zero) ->
  0 <= value < 2^256 -> (length xlimbs <= 5)%nat ->
  fe_at m b 0 xlimbs -> fe_at m b 40 (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 88 Cur Freeable -> Mem.load Mint32 m b 80 = Some (Vint flag) ->
  exists mf,
    Clight2.exec_stmt secp_ge empty_env le m (fn_body f_secp256k1_ge_neg) E0 le mf Out_normal /\
    fe_at mf b 0 xlimbs /\ fe_at mf b 40 (negate_values (write_fe_rho value 0)) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\ Mem.load Mint32 mf b 80 = Some (Vint flag) /\
    lframe (fun bx _ => bx <> b) m mf.
Proof.
  intros HR HA HV HLen HX HY HFree HFlag.
  destruct (exec_affine_negate_self_copy_owned le m b HR HA HFree)
    as (mc & HCopy & HUnchanged & HCopyFree).
  assert (HValid : Mem.valid_block m b).
  { eapply Mem.perm_valid_block; apply (HFree 0); lia. }
  assert (HXCopy : fe_at mc b 0 xlimbs).
  { eapply (owned_field_load_transport 0 88 m mc b xlimbs);
      [lia|exact HLen|exact HX|exact HCopyFree|].
    intros i Hi; eapply Mem.load_unchanged_on_1;
      [exact HUnchanged|exact HValid|intros;exact I]. }
  assert (HYCopy : fe_at mc b 40 (map Int64.repr (fe_limbs_of value))).
  { eapply (owned_field_load_transport 40 88 m mc b (map Int64.repr (fe_limbs_of value)));
      [lia|change (5 <= 5)%nat;lia|exact HY|exact HCopyFree|].
    intros i Hi; eapply Mem.load_unchanged_on_1;
      [exact HUnchanged|exact HValid|intros;exact I]. }
  assert (HFlagCopy : Mem.load Mint32 mc b 80 = Some (Vint flag)).
  { eapply Mem.load_unchanged_on; [exact HUnchanged|intros;exact I|exact HFlag]. }
  destruct (affine_y_arithmetic_output mc b value xlimbs flag HV HLen HXCopy HYCopy HCopyFree HFlagCopy)
    as (mw & mf & HW & HN & HXF & HYF & HFF & HFlagF & HF).
  exists mf; split.
  - rewrite affine_negate_helper_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le); [exact HCopy|].
    eapply exec_affine_negate_y_tail_from_calls; eassumption.
  - split; [exact HXF|]; split; [exact HYF|]; split; [exact HFF|]; split; [exact HFlagF|].
    eapply lframe_trans.
    + eapply lframe_implies; [apply lframe_unchanged;exact HUnchanged|intros;exact I].
    + eapply lframe_implies; [exact HF|].
      intros bx pos HOther _ HFoot.
      change (foot [(b,0)] (map rshape (owned_field_slice 40 88)) bx pos) in HFoot.
      destruct (owned_field_slice_foot_bounds 40 88 b bx pos HFoot) as [HE _]; contradiction.
Qed.

Definition affine_negate_helper_temps b : temp_env :=
  PTree.set _a (Vptr b Ptrofs.zero)
    (PTree.set _r (Vptr b Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_ge_neg))).
Lemma affine_negate_helper_entry m b :
  function_entry2 secp_ge f_secp256k1_ge_neg [Vptr b Ptrofs.zero; Vptr b Ptrofs.zero] m
    empty_env (affine_negate_helper_temps b) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY HE; cbn in HX,HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in HE;discriminate|congruence].
  - constructor.
  - reflexivity.
Qed.
Lemma affine_negate_helper_temp_r b :
  (affine_negate_helper_temps b)!_r = Some (Vptr b Ptrofs.zero).
Proof. unfold affine_negate_helper_temps; rewrite PTree.gso by discriminate; apply PTree.gss. Qed.
Lemma affine_negate_helper_temp_a b :
  (affine_negate_helper_temps b)!_a = Some (Vptr b Ptrofs.zero).
Proof. unfold affine_negate_helper_temps; apply PTree.gss. Qed.

Theorem eval_affine_negate_point_output m b value xlimbs flag :
  0 <= value < 2^256 -> (length xlimbs <= 5)%nat ->
  fe_at m b 0 xlimbs -> fe_at m b 40 (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 88 Cur Freeable -> Mem.load Mint32 m b 80 = Some (Vint flag) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_neg)
      [Vptr b Ptrofs.zero;Vptr b Ptrofs.zero] E0 mf Vundef /\
    fe_at mf b 0 xlimbs /\ fe_at mf b 40 (negate_values (write_fe_rho value 0)) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\ Mem.load Mint32 mf b 80 = Some (Vint flag) /\
    lframe (fun bx _ => bx <> b) m mf.
Proof.
  intros HV HLen HX HY HFree HFlag.
  destruct (exec_affine_negate_body_output (affine_negate_helper_temps b) m b value xlimbs flag
    (affine_negate_helper_temp_r b) (affine_negate_helper_temp_a b) HV HLen HX HY HFree HFlag)
    as (mf & HBody & HXF & HYF & HFF & HFlagF & HF).
  exists mf; split.
  - eapply eval_funcall_internal with (e := empty_env) (le1 := affine_negate_helper_temps b)
      (le2 := affine_negate_helper_temps b) (m1 := m) (m2 := mf) (out := Out_normal).
    + apply affine_negate_helper_entry.
    + exact HBody.
    + reflexivity.
    + reflexivity.
  - split; [exact HXF|]; split; [exact HYF|]; split; [exact HFF|]; split; assumption.
Qed.
Timeout 60 Print Assumptions eval_affine_negate_point_output.
