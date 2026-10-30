(** Original affine-to-native-storage coordinate copies and normalizers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fns C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_field_copy_owned C.jet_secp_fe_inv_prefix C.jet_secp_b32_exec
 C.jet_secp_square_columns C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_permissions
 C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition ge_storage_coordinate (k:bool) := if k then _y else _x.
Definition ge_storage_copy k := Sassign (Evar (ge_storage_coordinate k) curve_fe_type)
 (curve_affine_field (ge_storage_coordinate k) curve_fe_type).
Definition ge_storage_normalize k :=curve_call _secp256k1_fe_normalize_var f_secp256k1_fe_normalize_var None
 [curve_local_address (ge_storage_coordinate k)].
Definition ge_storage_prepare k :=Ssequence (ge_storage_copy k) (ge_storage_normalize k).
Lemma ge_storage_prepare_closed k:closed_stmtb secp_closed_helpers (ge_storage_prepare k)=true.
Proof. destruct k;vm_compute;reflexivity. Qed.
Theorem exec_ge_storage_prepare k w e le m bin bx:
 e!(ge_storage_coordinate k)=Some (bx,curve_fe_type) ->e!_secp256k1_fe_normalize_var=None ->
 le!_a=Some (Vptr bin Ptrofs.zero) ->plain_env e ->bin<>bx ->square_input_bounds w ->
 fe_at m bin (if k then 40 else 0) (words5 w) ->Mem.range_perm m bx 0 40 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m (ge_storage_prepare k) E0 le mf Out_normal /\
 fe_at mf bx 0 (map Int64.repr (fe_limbs_of (fe_inv_value w))) /\
 Mem.range_perm mf bx 0 40 Cur Freeable /\keeps_permissions m mf /\
 lframe (fun b _=>b<>bx) m mf /\readonly_preserved m mf.
Proof.
 intros Local Symbol A Plain Separate Bounds Input Free.
 assert (Source:eval_expr secp_ge e le m
  (curve_affine_field (ge_storage_coordinate k) curve_fe_type)
  (Vptr bin (Ptrofs.repr (if k then 40 else 0)))).
 { eapply eval_Elvalue.
   - apply (eval_curve_field e le m bin (ge_storage_coordinate k) (if k then 40 else 0) curve_fe_type);[destruct k;[right;left;reflexivity|left;reflexivity]|exact A].
   - apply deref_loc_copy;reflexivity. }
 destruct (exec_field_copy_owned e le m
  (curve_affine_field (ge_storage_coordinate k) curve_fe_type)
  (Evar (ge_storage_coordinate k) curve_fe_type) bin (if k then 40 else 0) bx 0 w
  eq_refl eq_refl Source ltac:(apply eval_Evar_local;exact Local) Separate Input
  ltac:(lia) ltac:(exists 0;reflexivity) ltac:(change (40<=18446744073709551615);lia) Free)
 as (mc & Copy & FieldC & PermC & FrameC).
 assert (FreeC:Mem.range_perm mc bx 0 40 Cur Freeable).
 { intros pos Range;apply PermC,Free;exact Range. }
 destruct (eval_fe_inv_normalize w mc bx Bounds FieldC FreeC)
 as (mf & Normalize & FieldN & FreeN & KeepN & FrameN).
 rewrite fe_inv_canonical_storage in FieldN.
 assert (Body:Clight2.exec_stmt secp_ge e le m (ge_storage_prepare k) E0 le mf Out_normal).
 { unfold ge_storage_prepare;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le).
   - exact Copy.
   - unfold ge_storage_normalize;eapply exec_curve_call with (vargs:=[Vptr bx Ptrofs.zero]) (v:=Vundef).
     + unfold secp_pure;repeat first [left;reflexivity|right].
     + exact Symbol.
     + eapply eval_Econs;[apply eval_curve_local;exact Local|reflexivity|constructor].
     + exact Normalize. }
 exists mf;split;[exact Body|];split;[exact FieldN|];split;[exact FreeN|];split.
 - intros b pos kind perm P;apply KeepN,PermC;exact P.
 - split.
   + eapply lframe_trans.
     * eapply lframe_implies;[exact FrameC|];intros b pos Other _;left;exact Other.
     * eapply lframe_implies;[exact FrameN|];intros b pos Other _ [Same _];congruence.
   + exact (secp_closed_stmt_preserved _ _ _ _ _ _ _ _ Body Plain (ge_storage_prepare_closed k)).
Qed.
