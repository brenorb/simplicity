(** Copy/square/multiply stage of the original square-root addition chain. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_fns
 C.jet_secp_field_copy_owned C.jet_secp_field_pair_multiply C.jet_secp_root_square_loop
 C.jet_secp_square_numeric C.jet_secp_multiply_checkpoint_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words field_pair_product.

Definition root_stage_copy dst src := Sassign (Evar dst curve_fe_type) (Evar src curve_fe_type).
Definition root_stage_mul dst rhs := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [curve_local_address dst;curve_local_address dst;curve_local_address rhs].
Definition root_stage n dst src rhs := Ssequence (root_stage_copy dst src)
 (Ssequence (root_square_for dst (Z.of_nat n)) (root_stage_mul dst rhs)).
Definition root_stage_words n w v := field_pair_product (root_square_words n w) v.

Lemma root_stage_sources :
 map (fun n => firstn 3 (skipn n (root_body_spine (fn_body f_secp256k1_fe_sqrt_var))))
   [5;8;11;14;17;20;23;26;29;32]%nat =
 map root_body_spine
  [root_stage 3 _x6 _x3 _x3;root_stage 3 _x9 _x6 _x3;
   root_stage 2 _x11 _x9 _x2;root_stage 11 _x22 _x11 _x11;
   root_stage 22 _x44 _x22 _x22;root_stage 44 _x88 _x44 _x44;
   root_stage 88 _x176 _x88 _x88;root_stage 44 _x220 _x176 _x44;
   root_stage 3 _x223 _x220 _x3;root_stage 23 _t1 _x223 _x22].
Proof. reflexivity. Qed.

Lemma root_field_words_unique m b w v :
 fe_at m b 0 (words5 w) -> fe_at m b 0 (words5 v) -> words5 w=words5 v.
Proof.
 intros (_ & _ & _ & _ & HW) (_ & _ & _ & _ & HV).
 apply nth_error_ext;intros [|[|[|[|[|n]]]]];cbn [words5 nth_error];try reflexivity;
 match goal with |- Some (w ?i)=Some (v ?i) =>
   pose proof (HW i (w i) eq_refl) as H;
   pose proof (HV i (v i) eq_refl) as K;rewrite H in K;injection K as ->;reflexivity
 end.
Qed.

Theorem exec_root_stage_owned n dst src rhs e le m bd bs bv w v :
 Z.of_nat n<=88 ->
 e!dst=Some (bd,curve_fe_type) -> e!src=Some (bs,curve_fe_type) -> e!rhs=Some (bv,curve_fe_type) ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> bd<>bs -> bd<>bv ->
 square_input_bounds w -> square_input_bounds v ->
 fe_at m bs 0 (words5 w) -> fe_at m bv 0 (words5 v) ->
 Mem.range_perm m bd 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
 Mem.range_perm m bv 0 40 Cur Freeable -> exists mf lef,
 Clight2.exec_stmt secp_ge e le m (root_stage n dst src rhs) E0 lef mf Out_normal /\
 fe_at mf bd 0 (words5 (root_stage_words n w v)) /\ fe_at mf bs 0 (words5 w) /\ fe_at mf bv 0 (words5 v) /\
 Mem.range_perm mf bd 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
 Mem.range_perm mf bv 0 40 Cur Freeable /\ square_input_bounds (root_stage_words n w v) /\
 radix_value (root_stage_words n w v) mod field_prime=
   (radix_value (root_square_words n w)*radix_value v) mod field_prime /\
 lef!_j=Some (Vint (Int.repr (Z.of_nat n))) /\ (forall k,k<>_j -> lef!k=le!k) /\
 lframe (fun b _=>b<>bd /\ b<>bv) m mf.
Proof.
 intros HN ED ES EV EQ EM DS DV BW BV W V FD FS FV.
 assert (EC : eval_expr secp_ge e le m (Evar src curve_fe_type) (Vptr bs Ptrofs.zero)).
 { eapply eval_Elvalue;[apply eval_Evar_local;exact ES|apply deref_loc_copy;reflexivity]. }
 destruct (exec_field_copy_owned e le m (Evar src curve_fe_type) (Evar dst curve_fe_type)
   bs 0 bd 0 w eq_refl eq_refl EC ltac:(apply eval_Evar_local;exact ED)
   ltac:(congruence) W ltac:(lia) ltac:(exists 0;lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia) FD)
   as (mc & Copy & WC & Perm & FC).
 assert (FrameC : lframe (fun b _=>b<>bd) m mc).
 { eapply lframe_implies;[exact FC|];intros b pos H _;left;exact H. }
 assert (FDC : Mem.range_perm mc bd 0 40 Cur Freeable).
 { intros pos HP;apply (proj2 (Perm bd pos Cur Freeable));apply FD;exact HP. }
 assert (VC : fe_at mc bv 0 (words5 v)).
 { eapply curve_keep_field_range;[reflexivity|exact V|exact FrameC|];intros;congruence. }
 assert (FVC : Mem.range_perm mc bv 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FV|exact FrameC|];intros;congruence. }
 destruct (exec_root_square_for_owned n dst e le mc bd w HN ED EQ BW WC FDC)
   as (ml & lel & Loop & WL & FDL & BL & JL & Temps & FrameL).
 assert (VL : fe_at ml bv 0 (words5 v)).
 { eapply curve_keep_field_range;[reflexivity|exact VC|exact FrameL|];intros;congruence. }
 assert (FVL : Mem.range_perm ml bv 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FVC|exact FrameL|];intros;congruence. }
 destruct (eval_field_pair_multiply (root_square_words n w) v ml bd bv BL BV DV WL VL FDL FVL)
   as (mf & Mul & WF & VF & FDF & FVF & Value & BF & Tight & FrameM).
 assert (CS : Clight2.exec_stmt secp_ge e lel ml (root_stage_mul dst rhs) E0 lel mf Out_normal).
 { unfold root_stage_mul;eapply exec_curve_call with
   (vargs:=[Vptr bd Ptrofs.zero;Vptr bd Ptrofs.zero;Vptr bv Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat (first [left;reflexivity|right]).
   - exact EM.
   - eapply eval_Econs;[apply eval_curve_local;exact ED|reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact ED|reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact EV|reflexivity|constructor].
   - exact Mul. }
 assert (FrameCL : lframe (fun b _=>b<>bd) m ml) by (eapply lframe_trans;eassumption).
 assert (WSL : fe_at ml bs 0 (words5 w)).
 { eapply curve_keep_field_range;[reflexivity|exact W|exact FrameCL|];intros;congruence. }
 assert (FSL : Mem.range_perm ml bs 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FS|exact FrameCL|];intros;congruence. }
 assert (WSF : fe_at mf bs 0 (words5 w)).
 { destruct (Pos.eq_dec bs bv) as [->|SV].
   - (* The copy source may also be the multiplier operand. *)
     rewrite (root_field_words_unique ml bv w v WSL VL);exact VF.
   - eapply curve_keep_field_range;[reflexivity|exact WSL|exact FrameM|];intros;split;congruence.
 }
 assert (FSF : Mem.range_perm mf bs 0 40 Cur Freeable).
 { destruct (Pos.eq_dec bs bv) as [->|SV];[exact FVF|].
   eapply curve_keep_free;[lia|exact FSL|exact FrameM|];intros;split;congruence. }
 exists mf,lel;split.
 - unfold root_stage;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mc).
   + exact Copy.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lel) (m1:=ml);eassumption.
 - split;[exact WF|];split;[exact WSF|];split;[exact VF|];split;[exact FDF|].
   split;[exact FSF|];split;[exact FVF|];split;[exact BF|];split;[exact Value|].
   split;[exact JL|];split;[exact Temps|].
   eapply lframe_trans;[|exact FrameM].
   eapply lframe_implies;[exact FrameCL|];intros b pos H _;exact (proj1 H).
Qed.
