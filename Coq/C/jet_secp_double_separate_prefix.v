(** First five original arithmetic calls for distinct-source doubling.
    This closes the first arithmetic prefix needed by odd-multiple table
    construction; it is not a whole doubling or public jet theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_double_separate_product
 C.jet_secp_point_square_coordinate C.jet_secp_point_write_run C.jet_secp_curve_square
 C.jet_secp_gej_curve_coordinate
 C.jet_secp_double_l_scale C.jet_secp_field_mul_small C.jet_secp_field_half_numeric
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_double_statements C.jet_secp_curve_statements C.jet_secp_statement_prefix.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words double_l_words.

Definition double_separate_prefix := statement_sequence
 (firstn 5 (fst (split_statement_last double_arithmetic_body))) Sskip.
Lemma double_separate_prefix_source : double_separate_prefix=
 Ssequence (curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
   [double_point_address _r _z;double_point_address _a _z;double_point_address _a _y])
 (Ssequence (curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
   [curve_local_address _s;double_point_address _a _y])
 (Ssequence (curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
   [curve_local_address _l;double_point_address _a _x])
 (Ssequence (curve_call _secp256k1_fe_mul_int f_secp256k1_fe_mul_int None
   [curve_local_address _l;Econst_int (Int.repr 3) tint])
 (Ssequence (curve_call _secp256k1_fe_half f_secp256k1_fe_half None
   [curve_local_address _l]) Sskip)))).
Proof. reflexivity. Qed.

Local Ltac prefix_args HA HR := first [apply eval_Enil |
 eapply eval_Econs;
  [first [apply eval_curve_local;reflexivity |
    apply eval_double_point_address;[cbn [In];tauto|first [exact HA|exact HR]] | constructor]
  |reflexivity|prefix_args HA HR]].
Local Ltac prefix_call HA HR Call := lazymatch type of Call with
 | Clight2.eval_funcall _ _ _ ?args _ _ ?value =>
 eapply exec_curve_call with (vargs:=args) (v:=value);
  [unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]) |
   reflexivity | prefix_args HA HR | exact Call] end.

Theorem exec_double_separate_prefix le x y z m br ba bs bl bt :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 br<>ba -> br<>bs -> br<>bl -> ba<>bs -> ba<>bl -> bs<>bl ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bl 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge (double_helper_env bl bs bt) le m double_separate_prefix E0 le mf Out_normal /\
 fe_at mf br 80 (words5 (point_mul_words z y)) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 fe_at mf bs 0 (words5 (square_words y)) /\
 fe_at mf bl 0 (words5 (double_l_words (square_words x))) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bl 0 40 Cur Freeable /\
 square_input_bounds (point_mul_words z y) /\ mul_small_input_bounds (square_words y) /\
 square_input_bounds (double_l_words (square_words x)) /\
 lframe (fun b pos=>b<>bs /\ b<>bl /\
   (b<>br \/ pos<80 \/ 120<=pos) /\ (b<>ba \/ pos<0 \/ 120<=pos)) m mf.
Proof.
 intros HA HR BX BY BZ RA RS RL AS AL SL X Y ZAt RF AF SF LF.
 destruct (eval_double_separate_product z y m br ba BZ BY RA RF ZAt Y AF)
  as (m1 & C1 & RZ1 & Z1 & Y1 & RF1 & AF1 & VZ & BZ1 & F1).
 assert (X1:fe_at m1 ba 0 (words5 x)).
 { eapply curve_keep_field_range;[reflexivity|exact X|exact F1|].
   intros pos Range;split;[left;congruence|right;left;lia]. }
 assert (SF1:Mem.range_perm m1 bs 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact SF|exact F1|];intros;split;left;congruence. }
 assert (LF1:Mem.range_perm m1 bl 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact LF|exact F1|];intros;split;left;congruence. }
 destruct (eval_point_square_coordinate PointY y m1 bs ba BY SF1 Y1 AF1 (not_eq_sym AS))
  as (m2 & C2 & S2 & SF2 & Y2 & AF2 & VS & BS2 & BTS & F2).
 pose proof (coordinate_frame_blocks PointY bs ba m1 m2 F2) as E2.
 pose proof (coordinate_frame_other PointY PointX x m1 m2 bs ba ltac:(discriminate)
   (not_eq_sym AS) X1 F2) as X2.
 pose proof (coordinate_frame_other PointY PointZ z m1 m2 bs ba ltac:(discriminate)
   (not_eq_sym AS) Z1 F2) as Z2.
 assert (RZ2:fe_at m2 br 80 (words5 (point_mul_words z y))).
 { eapply field_at_lframe;[exact RZ1|exact E2|];intros;split;congruence. }
 assert (RF2:Mem.range_perm m2 br 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact RF1|exact E2|];intros;split;congruence. }
 assert (LF2:Mem.range_perm m2 bl 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact LF1|exact E2|];intros;split;congruence. }
 destruct (eval_point_square_coordinate PointX x m2 bl ba BX LF2 X2 AF2 (not_eq_sym AL))
  as (m3 & C3 & L3 & LF3 & X3 & AF3 & VX & BL3 & BTL & F3).
 pose proof (coordinate_frame_blocks PointX bl ba m2 m3 F3) as E3.
 pose proof (coordinate_frame_other PointX PointY y m2 m3 bl ba ltac:(discriminate)
   (not_eq_sym AL) Y2 F3) as Y3.
 pose proof (coordinate_frame_other PointX PointZ z m2 m3 bl ba ltac:(discriminate)
   (not_eq_sym AL) Z2 F3) as Z3.
 assert (RZ3:fe_at m3 br 80 (words5 (point_mul_words z y))).
 { eapply field_at_lframe;[exact RZ2|exact E3|];intros;split;congruence. }
 assert (RF3:Mem.range_perm m3 br 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact RF2|exact E3|];intros;split;congruence. }
 assert (S3:fe_at m3 bs 0 (words5 (square_words y))).
 { eapply field_at_lframe;[exact S2|exact E3|];intros;split;congruence. }
 assert (SF3:Mem.range_perm m3 bs 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact SF2|exact E3|];intros;split;congruence. }
 assert (BLT:mul_small_input_bounds (square_words x)) by (intros i HI;exact (proj2 (BTL i HI))).
 destruct (eval_double_l_scale (square_words x) m3 bl BLT L3 LF3)
  as (m4 & mf & C4 & C5 & L5 & LF5 & BL5 & VL & F45).
 assert (RZF:fe_at mf br 80 (words5 (point_mul_words z y))).
 { eapply field_at_lframe;[exact RZ3|exact F45|];intros;congruence. }
 assert (XF:fe_at mf ba 0 (words5 x)).
 { eapply field_at_lframe;[exact X3|exact F45|];intros;congruence. }
 assert (YF:fe_at mf ba 40 (words5 y)).
 { eapply field_at_lframe;[exact Y3|exact F45|];intros;congruence. }
 assert (ZF:fe_at mf ba 80 (words5 z)).
 { eapply field_at_lframe;[exact Z3|exact F45|];intros;congruence. }
 assert (SFld:fe_at mf bs 0 (words5 (square_words y))).
 { eapply field_at_lframe;[exact S3|exact F45|];intros;congruence. }
 assert (RFF:Mem.range_perm mf br 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact RF3|exact F45|];intros;congruence. }
 assert (AFF:Mem.range_perm mf ba 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact AF3|exact F45|];intros;congruence. }
 assert (SFF:Mem.range_perm mf bs 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact SF3|exact F45|];intros;congruence. }
 exists mf;split.
 - rewrite double_separate_prefix_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le);[prefix_call HA HR C1|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le);[prefix_call HA HR C2|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le);[prefix_call HA HR C3|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m4) (le1:=le);[prefix_call HA HR C4|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le);[prefix_call HA HR C5|constructor].
 - split;[exact RZF|];split;[exact XF|];split;[exact YF|];split;[exact ZF|];
   split;[exact SFld|];split;[exact L5|];split;[exact RFF|];split;[exact AFF|];
   split;[exact SFF|];split;[exact LF5|];split;[exact BZ1|];
   split;[intros i HI;exact (proj2 (BTS i HI))|];split;[exact BL5|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact F1|].
     intros b pos (NS & NL & NR & NA) Valid;split;[exact NR|].
     destruct NA as [NA|[NA|NA]];[left;exact NA|right;left;lia|right;right;exact NA].
   + eapply lframe_trans.
     * eapply lframe_implies;[exact F2|].
       intros b pos (NS & NL & NR & NA) Valid.
       unfold point_square_coordinate_frame;intros [[Same Range]|[Same Range]];
         [congruence|subst b;destruct NA as [NA|[NA|NA]];cbn [point_coordinate_offset] in Range;intuition lia].
     * eapply lframe_trans.
       -- eapply lframe_implies;[exact F3|].
          intros b pos (NS & NL & NR & NA) Valid.
          unfold point_square_coordinate_frame;intros [[Same Range]|[Same Range]];
            [congruence|subst b;destruct NA as [NA|[NA|NA]];cbn [point_coordinate_offset] in Range;intuition lia].
       -- eapply lframe_implies;[exact F45|].
          intros b pos (NS & NL & NR & NA) Valid;exact NL.
Qed.
