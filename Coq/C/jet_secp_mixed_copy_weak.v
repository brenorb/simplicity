(** The two original copied/weak-normalized coordinates in mixed addition.
    Destination contents are uninitialized; all call results come from storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_statements C.jet_secp_double_statements
  C.jet_secp_mixed_finite_start C.jet_secp_field_copy_owned C.jet_secp_field_weak_tight
  C.jet_secp_curve_frame C.jet_secp_field_read_preservation.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_copy_coordinate (y : bool) := Sassign
  (Evar (if y then _s1 else _u1) curve_fe_type)
  (double_point_field _a (if y then _y else _x) curve_fe_type).
Definition mixed_weak_coordinate (y : bool) := curve_call _secp256k1_fe_normalize_weak
  f_secp256k1_fe_normalize_weak None [curve_local_address (if y then _s1 else _u1)].
Definition mixed_after_u1 := match mixed_after_square with
  | Ssequence _ (Ssequence _ rest) => rest | _ => Sskip end.
Definition mixed_u2_stmt := match mixed_after_u1 with | Ssequence h _ => h | _ => Sskip end.
Definition mixed_after_s1 := match mixed_after_u1 with
  | Ssequence _ (Ssequence _ (Ssequence _ rest)) => rest | _ => Sskip end.
Lemma mixed_copies_source : mixed_after_square=
  Ssequence (mixed_copy_coordinate false) (Ssequence (mixed_weak_coordinate false)
    (Ssequence mixed_u2_stmt (Ssequence (mixed_copy_coordinate true)
      (Ssequence (mixed_weak_coordinate true) mixed_after_s1)))).
Proof. reflexivity. Qed.

Lemma eval_mixed_a_copy_field e le m ba (y : bool) : le!_a=Some (Vptr ba Ptrofs.zero) ->
  eval_lvalue secp_ge e le m (double_point_field _a (if y then _y else _x) curve_fe_type)
    ba (Ptrofs.repr (if y then 40 else 0)) Full.
Proof.
  intro HA;pose proof (eval_double_point_address e le m ba _a (if y then _y else _x)
    (if y then 40 else 0) ltac:(destruct y;cbn [In];tauto) HA) as HE.
  unfold double_point_address in HE;inversion HE;subst;[assumption|].
  match goal with HL : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion HL end.
Qed.

Theorem exec_mixed_copy_weak e le m ba bu (y : bool) w :
  le!_a=Some (Vptr ba Ptrofs.zero) -> e!(if y then _s1 else _u1)=Some (bu,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> ba<>bu ->
  fe_limbs_ok (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
    (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) ->
  fe_at m ba (if y then 40 else 0) (words5 w) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bu 0 40 Cur Freeable ->
  exists mc mf,
  Clight2.exec_stmt secp_ge e le m (mixed_copy_coordinate y) E0 le mc Out_normal /\
  Clight2.exec_stmt secp_ge e le mc (mixed_weak_coordinate y) E0 le mf Out_normal /\
  fe_at mf bu 0 (words5 w) /\ Mem.range_perm mf bu 0 40 Cur Freeable /\
  fe_at mf ba (if y then 40 else 0) (words5 w) /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
  lframe (fun b _=>b<>bu) m mf.
Proof.
  intros HA HU HE HSep HB HField HFA HFU.
  destruct (exec_field_copy_owned e le m
    (double_point_field _a (if y then _y else _x) curve_fe_type)
    (Evar (if y then _s1 else _u1) curve_fe_type)
    ba (if y then 40 else 0) bu 0 w eq_refl eq_refl
    ltac:(eapply eval_Elvalue;[apply eval_mixed_a_copy_field;exact HA|apply deref_loc_copy;reflexivity])
    ltac:(apply eval_Evar_local;exact HU) HSep HField ltac:(lia) ltac:(exists 0;reflexivity)
    ltac:(change (40<=18446744073709551615);lia) HFU)
    as (mc & CC & FC & PC & FrameC).
  assert (HFUc : Mem.range_perm mc bu 0 40 Cur Freeable).
  { intros pos HP;apply (proj2 (PC bu pos Cur Freeable));apply HFU;exact HP. }
  destruct (eval_field_weak_tight w mc bu HB FC HFUc) as (mf & CW & FF & HFUf & FrameW).
  assert (Frame : lframe (fun b _=>b<>bu) m mf).
  { eapply lframe_trans;[|exact FrameW].
    eapply lframe_implies;[exact FrameC|];intros b pos HN HV;left;exact HN. }
  exists mc,mf;split;[exact CC|];split.
  - unfold mixed_weak_coordinate;eapply exec_curve_call with (vargs:=[Vptr bu Ptrofs.zero]) (v:=Vundef).
    + unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
    + exact HE.
    + eapply eval_Econs;[apply eval_curve_local;exact HU|reflexivity|constructor].
    + exact CW.
  - split;[exact FF|];split;[exact HFUf|];split.
    + eapply field_at_lframe;[exact HField|exact Frame|];intros;exact HSep.
    + split;[|exact Frame];eapply curve_keep_free;[lia|exact HFA|exact Frame|];intros;exact HSep.
Qed.
