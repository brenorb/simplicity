(** Actual affine storage-saving body: copies, normalization and both packers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Errors.
Require Import C.jet_sx_state C.jet_sx_mem C.jet_secp_fns C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_fe_inv_prefix C.jet_secp_b32_exec
 C.jet_secp_square_columns C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_permissions
 C.jet_clight_internal_preserve C.jet_secp_pubkey_copy C.jet_secp_affine_storage
 C.jet_secp_storage_pack C.jet_secp_storage_pack_numeric C.jet_secp_storage_pack_owned
 C.jet_secp_storage_unpack C.jet_secp_storage_numeric.
Require Import C.jet_secp_ge_storage_prepare.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition ge_storage_output_address k:=Eaddrof
 (Efield (Ederef (Etempvar _r (tptr pubkey_storage_type)) pubkey_storage_type)
 (ge_storage_coordinate k) (Tstruct __5469 noattr)) (tptr (Tstruct __5469 noattr)).
Definition ge_storage_pack k:=curve_call _secp256k1_fe_to_storage f_secp256k1_fe_to_storage None
 [ge_storage_output_address k;curve_local_address (ge_storage_coordinate k)].
Definition ge_storage_tail:=Ssequence (ge_storage_pack false) (ge_storage_pack true).
Lemma ge_storage_body_source:fn_body f_secp256k1_ge_to_storage=
 Ssequence (Sloop Sskip Sbreak)
 (Ssequence (ge_storage_copy false) (Ssequence (ge_storage_normalize false)
 (Ssequence (ge_storage_copy true) (Ssequence (ge_storage_normalize true) ge_storage_tail)))).
Proof. reflexivity. Qed.
Lemma ge_storage_layout k:exists co,(genv_cenv secp_ge)!__6125=Some co /\
 field_offset secp_ge (ge_storage_coordinate k) (co_members co)=OK ((if k then 32 else 0),Full).
Proof.
 assert (Members:option_map co_members ((genv_cenv secp_ge)!__6125)=
  Some [Member_plain _x (Tstruct __5469 noattr);Member_plain _y (Tstruct __5469 noattr)])
 by (vm_compute;reflexivity).
 destruct ((genv_cenv secp_ge)!__6125) as [co|] eqn:Layout;[|discriminate].
 exists co;split;[reflexivity|];inversion Members as [Fields];rewrite Fields.
 destruct k;vm_compute;reflexivity.
Qed.
Lemma eval_ge_storage_output_address k e le m bout:
 le!_r=Some (Vptr bout Ptrofs.zero) ->
 eval_expr secp_ge e le m (ge_storage_output_address k) (Vptr bout (Ptrofs.repr (if k then 32 else 0))).
Proof.
 intro R;destruct (ge_storage_layout k) as (co & Layout & Offset).
 unfold ge_storage_output_address;apply eval_Eaddrof;
 rewrite <-(Ptrofs.add_zero_l (Ptrofs.repr (if k then 32 else 0))).
 eapply eval_Efield_struct with (co:=co) (delta:=(if k then 32 else 0)).
 - eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact R|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Layout.
 - exact Offset.
Qed.
Lemma exec_ge_storage_pack_call k e le m mf bout bx:
 e!_secp256k1_fe_to_storage=None ->e!(ge_storage_coordinate k)=Some (bx,curve_fe_type) ->
 le!_r=Some (Vptr bout Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_to_storage)
 [Vptr bout (Ptrofs.repr (if k then 32 else 0));Vptr bx Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m (ge_storage_pack k) E0 le mf Out_normal.
Proof.
 intros Symbol Local R Call;unfold ge_storage_pack;eapply exec_curve_call with
 (vargs:=[Vptr bout (Ptrofs.repr (if k then 32 else 0));Vptr bx Ptrofs.zero]) (v:=Vundef).
 - unfold secp_pure;repeat first [left;reflexivity|right].
 - exact Symbol.
 - eapply eval_Econs;[apply eval_ge_storage_output_address;exact R|reflexivity|].
   eapply eval_Econs;[apply eval_curve_local;exact Local|reflexivity|constructor].
 - exact Call.
Qed.
Lemma field_storage_readable_frame w m mf b base P:
 field_storage_readable m b base w ->lframe P m mf ->
 (forall pos,base<=pos<base+32 ->P b pos) ->field_storage_readable mf b base w.
Proof.
 intros (Base & Align & Max & Perm & Loads) Frame Outside.
 assert (Valid:Mem.valid_block m b) by (eapply Mem.perm_valid_block;apply (Perm base);lia).
 repeat split;try assumption.
 - intros pos Range;apply (proj1 (proj2 Frame));[exact Valid|apply Outside;exact Range|apply Perm;exact Range].
 - intros i Bound;rewrite (proj1 Frame Mint64 b (base+8*Z.of_nat i) Valid);[apply Loads;exact Bound|].
   intros pos Range;apply Outside;change (size_chunk Mint64) with 8 in Range;lia.
Qed.
Definition ge_storage_words wx wy i:=if (i<?4)%nat
 then storage_pack_words (limb_rho (fe_inv_value wx)) i
 else storage_pack_words (limb_rho (fe_inv_value wy)) (i-4)%nat.
Lemma ge_storage_words_values wx wy:
 field_storage_value (ge_storage_words wx wy)=fe_inv_value wx /\
 field_storage_value (fun i=>ge_storage_words wx wy (4+i)%nat)=fe_inv_value wy.
Proof.
 split.
 - change (field_storage_value (storage_pack_words (limb_rho (fe_inv_value wx)))=fe_inv_value wx).
   apply storage_pack_canonical;apply (proj2 (fe_inv_value_range wx)).
 - change (field_storage_value (storage_pack_words (limb_rho (fe_inv_value wy)))=fe_inv_value wy).
   apply storage_pack_canonical;apply (proj2 (fe_inv_value_range wy)).
Qed.
Lemma ge_storage_readable_pair wx wy m b:
 field_storage_readable m b 0 (storage_pack_words (limb_rho (fe_inv_value wx))) ->
 field_storage_readable m b 32 (storage_pack_words (limb_rho (fe_inv_value wy))) ->
 affine_storage_readable m b 0 (ge_storage_words wx wy).
Proof.
 intros (BX & AX & MX & PX & LX) (BY & AY & MY & PY & LY).
 split;[lia|];split;[exact AX|];split;[lia|];split.
 - intros pos Range;destruct (Z_lt_dec pos 32);[apply PX;lia|apply PY;lia].
 - intros i Bound;destruct i as [|[|[|[|[|[|[|[|i]]]]]]]];try lia;
   first [apply LX;lia|exact (LY 0%nat ltac:(lia))|exact (LY 1%nat ltac:(lia))|
    exact (LY 2%nat ltac:(lia))|exact (LY 3%nat ltac:(lia))].
Qed.
Lemma exec_normal_pair_then ge e le m first second last le1 m1 le2 m2 out:
 Clight2.exec_stmt ge e le m (Ssequence first second) E0 le1 m1 Out_normal ->
 Clight2.exec_stmt ge e le1 m1 last E0 le2 m2 out ->
 Clight2.exec_stmt ge e le m (Ssequence first (Ssequence second last)) E0 le2 m2 out.
Proof.
 intros Pair Last;inversion Pair;subst;[|contradiction].
 match goal with H:?t1**?t2=E0|-_=>destruct (Eapp_E0_inv t1 t2 H) as [-> ->] end.
 change E0 with (E0**(E0**E0));eapply exec_Sseq_1;[eassumption|].
 eapply exec_Sseq_1;[eassumption|exact Last].
Qed.
Theorem exec_ge_to_storage_body wx wy e le m bin bout bx b_y:
 e!_x=Some (bx,curve_fe_type) ->e!_y=Some (b_y,curve_fe_type) ->
 e!_secp256k1_fe_normalize_var=None ->e!_secp256k1_fe_to_storage=None ->plain_env e ->
 le!_a=Some (Vptr bin Ptrofs.zero) ->le!_r=Some (Vptr bout Ptrofs.zero) ->
 bin<>bx ->bin<>b_y ->NoDup [bout;bx;b_y] ->
 square_input_bounds wx ->square_input_bounds wy ->
 fe_at m bin 0 (words5 wx) ->fe_at m bin 40 (words5 wy) ->
 (forall b hi,In (b,hi) [(bout,64);(bx,40);(b_y,40)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_ge_to_storage) E0 le mf Out_normal /\
 affine_storage_readable mf bout 0 (ge_storage_words wx wy) /\
 (forall b hi,In (b,hi) [(bout,64);(bx,40);(b_y,40)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bout /\b<>bx /\b<>b_y) m mf /\readonly_preserved m mf.
Proof.
 intros X Y NormalizeSym PackSym Plain A R SourceX SourceY Separate BoundsX BoundsY InputX InputY Owned.
 assert (OX:bout<>bx /\bout<>b_y /\bx<>b_y).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 destruct OX as (OutX & OutY & XY).
 destruct (exec_ge_storage_prepare false wx e le m bin bx X NormalizeSym A Plain SourceX BoundsX InputX
  (Owned bx 40 ltac:(clear;cbn [In];tauto)))
 as (mx & PrepareX & FieldX & FreeX & KeepX & FrameX & ReadX).
 assert (InputYX:fe_at mx bin 40 (words5 wy)).
 { eapply field_at_lframe;[exact InputY|exact FrameX|intros;exact SourceX]. }
 destruct (exec_ge_storage_prepare true wy e le mx bin b_y Y NormalizeSym A Plain SourceY BoundsY InputYX
  ltac:(intros pos Range;apply KeepX;exact (Owned b_y 40 ltac:(clear;cbn [In];tauto) pos Range)))
 as (my & PrepareY & FieldY & FreeY & KeepY & FrameY & ReadY).
 assert (FieldXY:fe_at my bx 0 (map Int64.repr (fe_limbs_of (fe_inv_value wx)))).
 { eapply field_at_lframe;[exact FieldX|exact FrameY|intros;exact XY]. }
 assert (OwnedY:forall b hi,In (b,hi) [(bout,64);(bx,40);(b_y,40)] ->Mem.range_perm my b 0 hi Cur Freeable).
 { intros b hi Slot pos Range;apply KeepY,KeepX;exact (Owned b hi Slot pos Range). }
 destruct (eval_fe_to_storage_owned (fe_inv_value wx) my bout 0 bx 0
  (proj2 (fe_inv_value_range wx)) OutX ltac:(lia) ltac:(exists 0;reflexivity)
  ltac:(change (32<=18446744073709551615);lia)
  ltac:(intros pos Range;apply (OwnedY bout 64 ltac:(clear;cbn [In];tauto));lia) FieldXY)
 as (mpx & PackX & StorageX & ValueX & FieldXP & KeepPX & FramePX & ReadPX).
 assert (FieldYP:fe_at mpx b_y 0 (map Int64.repr (fe_limbs_of (fe_inv_value wy)))).
 { eapply field_at_lframe;[exact FieldY|exact FramePX|].
   intros pos Foot;destruct (storage_pack_foot_bounds bout 0 bx 0 b_y pos Foot)
   as [[Same _]|[Same _]];congruence. }
 destruct (eval_fe_to_storage_owned (fe_inv_value wy) mpx bout 32 b_y 0
  (proj2 (fe_inv_value_range wy)) OutY ltac:(lia) ltac:(exists 4;reflexivity)
  ltac:(change (64<=18446744073709551615);lia)
  ltac:(intros pos Range;apply KeepPX;apply (OwnedY bout 64 ltac:(clear;cbn [In];tauto));lia) FieldYP)
 as (mf & PackY & StorageY & ValueY & FieldYF & KeepPY & FramePY & ReadPY).
 assert (StorageXF:field_storage_readable mf bout 0 (storage_pack_words (limb_rho (fe_inv_value wx)))).
 { eapply field_storage_readable_frame;[exact StorageX|exact FramePY|].
   intros pos Range Foot;destruct (storage_pack_foot_bounds bout 32 b_y 0 bout pos Foot)
   as [[_ Pos]|[Same _]];[lia|congruence]. }
 assert (PackBody:Clight2.exec_stmt secp_ge e le my ge_storage_tail E0 le mf Out_normal).
 { unfold ge_storage_tail;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mpx) (le1:=le).
   - exact (exec_ge_storage_pack_call false e le my mpx bout bx PackSym X R PackX).
   - exact (exec_ge_storage_pack_call true e le mpx mf bout b_y PackSym Y R PackY). }
 exists mf;split.
 - rewrite ge_storage_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le).
   + eapply exec_Sloop_stop2 with (out1:=Out_normal) (out2:=Out_break) (t1:=E0) (t2:=E0);
     constructor.
   + eapply exec_normal_pair_then;[exact PrepareX|].
     eapply exec_normal_pair_then;[exact PrepareY|exact PackBody].
 - split;[exact (ge_storage_readable_pair wx wy mf bout StorageXF StorageY)|];split.
   + intros b hi Slot pos Range;apply KeepPY,KeepPX;exact (OwnedY b hi Slot pos Range).
   + split.
     * eapply lframe_trans.
       { eapply lframe_implies;[exact FrameX|];intros b pos (_ & Outside & _) _;exact Outside. }
       eapply lframe_trans.
       { eapply lframe_implies;[exact FrameY|];intros b pos (_ & _ & Outside) _;exact Outside. }
       eapply lframe_trans.
       { eapply lframe_implies;[exact FramePX|].
         intros b pos (Out & NX & _) _ Foot;
          destruct (storage_pack_foot_bounds bout 0 bx 0 b pos Foot) as [[Same _]|[Same _]];congruence. }
       { eapply lframe_implies;[exact FramePY|].
         intros b pos (Out & _ & NY) _ Foot;
          destruct (storage_pack_foot_bounds bout 32 b_y 0 b pos Foot) as [[Same _]|[Same _]];congruence. }
     * eapply preserved_trans;[exact ReadX|];eapply preserved_trans;[exact ReadY|].
       eapply preserved_trans;[exact ReadPX|exact ReadPY].
Qed.
