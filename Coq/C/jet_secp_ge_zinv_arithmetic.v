(** All four original arithmetic calls of ge_set_gej_zinv. Factor storage is
    either a 40-byte field or the Z slice of a 128-byte point; the affine
    destination can be the first entry of a larger table allocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_ge_zinv_factor C.jet_secp_ge_zinv_statements C.jet_secp_affine_gej_product
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_curve_statements
 C.jet_secp_double_statements C.jet_secp_curve_square C.jet_secp_point_write_run
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage
 C.jet_secp_multiply_normalize_bridge.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words.

Definition ge_zinv_x_words x zi := point_mul_words x (square_words zi).
Definition ge_zinv_y_words y zi := point_mul_words y (point_mul_words (square_words zi) zi).
Definition ge_zinv_arithmetic_frame (br ba bf b2 b3 b:block) (pos:Z) :=
 b<>b2 /\ b<>b3 /\ b<>bf /\ (b<>br \/ pos<0 \/ 80<=pos) /\ (b<>ba \/ pos<0 \/ 80<=pos).

Local Ltac run_ge_call Call := lazymatch type of Call with
 | Clight2.eval_funcall _ _ _ ?args _ _ ?value=>
 eapply exec_curve_call with (vargs:=args) (v:=value);
  [unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]) |
   reflexivity | |exact Call] end.
Local Ltac args_square ZI := eapply eval_Econs;
 [apply eval_curve_local;reflexivity|reflexivity|];
 eapply eval_Econs;[apply eval_Etempvar;exact ZI|reflexivity|constructor].
Local Ltac args_cube ZI := eapply eval_Econs;
 [apply eval_curve_local;reflexivity|reflexivity|args_square ZI].
Local Ltac args_product Y R A :=
 eapply eval_Econs;[apply eval_ge_zinv_result_address with (y:=Y);exact R|reflexivity|];
 eapply eval_Econs;
 [apply eval_double_point_address;[destruct Y;cbn [curve_square_offset In];tauto|exact A]|reflexivity|];
 eapply eval_Econs;[apply eval_curve_local;reflexivity|reflexivity|constructor].

Theorem exec_ge_zinv_arithmetic le point size x y zi m br ba bf b2 b3 :
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_a=Some (Vptr ba Ptrofs.zero) ->
 le!_zi=Some (Vptr bf (Ptrofs.repr (ge_zinv_factor_offset point))) ->
 88<=size -> size<=Ptrofs.max_unsigned -> NoDup [br;ba;bf;b2;b3] ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds zi ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) ->
 fe_at m bf (ge_zinv_factor_offset point) (words5 zi) ->
 Mem.range_perm m br 0 size Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bf 0 (ge_zinv_factor_size point) Cur Freeable ->
 Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge (ge_zinv_env b2 b3) le m ge_zinv_arithmetic E0 le mf Out_normal /\
 fe_at mf br 0 (words5 (ge_zinv_x_words x zi)) /\ fe_at mf br 40 (words5 (ge_zinv_y_words y zi)) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
 fe_at mf bf (ge_zinv_factor_offset point) (words5 zi) /\
 Mem.range_perm mf br 0 size Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bf 0 (ge_zinv_factor_size point) Cur Freeable /\
 Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
 square_input_bounds (ge_zinv_x_words x zi) /\ square_input_bounds (ge_zinv_y_words y zi) /\
 lframe (ge_zinv_arithmetic_frame br ba bf b2 b3) m mf.
Proof.
 intros R A ZI Size Max Sep BX BY BZI X Y Factor RF AF FF F2 F3.
 assert (RA:br<>ba) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
 assert (RB:br<>bf) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
 assert (R2:br<>b2) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
 assert (R3:br<>b3) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
 assert (AB:ba<>bf) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
 assert (A2:ba<>b2) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
 assert (A3:ba<>b3) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
 assert (B2:bf<>b2) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
 assert (B3:bf<>b3) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
 assert (S23:b2<>b3) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
 assert (FactorSize:0<ge_zinv_factor_size point) by (destruct point;cbn [ge_zinv_factor_size];lia).
 destruct (eval_ge_zinv_factor_square point zi m b2 bf BZI (not_eq_sym B2) F2 Factor FF)
  as (m1 & C1 & Z2 & F21 & Factor1 & FF1 & BZI2 & Frame1).
 assert (X1:fe_at m1 ba 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact Frame1|];intros;split;congruence).
 assert (Y1:fe_at m1 ba 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact Frame1|];intros;split;congruence).
 assert (RF1:Mem.range_perm m1 br 0 size Cur Freeable) by
  (eapply curve_keep_free;[lia|exact RF|exact Frame1|];intros;split;congruence).
 assert (AF1:Mem.range_perm m1 ba 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact AF|exact Frame1|];intros;split;congruence).
 assert (F31:Mem.range_perm m1 b3 0 40 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact F3|exact Frame1|];intros;split;congruence).
 destruct (eval_ge_zinv_factor_cube point (square_words zi) zi m1 b3 b2 bf BZI2 BZI
   (not_eq_sym S23) (not_eq_sym B3) (not_eq_sym B2) F31 Z2 F21 Factor1 FF1)
  as (m2 & C2 & Z3 & Z22 & Factor2 & F32 & F22 & FF2 & BZI3 & Frame2).
 assert (X2:fe_at m2 ba 0 (words5 x)) by
  (eapply field_at_lframe;[exact X1|exact Frame2|];intros;repeat split;congruence).
 assert (Y2:fe_at m2 ba 40 (words5 y)) by
  (eapply field_at_lframe;[exact Y1|exact Frame2|];intros;repeat split;congruence).
 assert (RF2:Mem.range_perm m2 br 0 size Cur Freeable) by
  (eapply curve_keep_free;[lia|exact RF1|exact Frame2|];intros;repeat split;congruence).
 assert (AF2:Mem.range_perm m2 ba 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact AF1|exact Frame2|];intros;repeat split;congruence).
 destruct (eval_affine_gej_product false size x (square_words zi) m2 br ba b2 Size Max BX BZI2
   RA R2 A2 RF2 X2 AF2 Z22 F22)
  as (m3 & C3 & RX3 & AX3 & Z23 & RF3 & AF3 & F23 & VX & BXO & Frame3).
 assert (AY3:fe_at m3 ba 40 (words5 y)).
 { eapply curve_keep_field_range;[reflexivity|exact Y2|exact Frame3|].
   intros pos Range;repeat split;try congruence;[left;congruence|right;right;cbn [curve_square_offset];lia]. }
 assert (Z33:fe_at m3 b3 0 (words5 (point_mul_words (square_words zi) zi))) by
  (eapply field_at_lframe;[exact Z3|exact Frame3|];intros;repeat split;try congruence;left;congruence).
 assert (F33:Mem.range_perm m3 b3 0 40 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact F32|exact Frame3|];intros;repeat split;try congruence;left;congruence).
 assert (Factor3:fe_at m3 bf (ge_zinv_factor_offset point) (words5 zi)) by
  (eapply field_at_lframe;[exact Factor2|exact Frame3|];intros;repeat split;try congruence;left;congruence).
 assert (FF3:Mem.range_perm m3 bf 0 (ge_zinv_factor_size point) Cur Freeable) by
  (eapply curve_keep_free;[exact FactorSize|exact FF2|exact Frame3|];intros;repeat split;try congruence;left;congruence).
 destruct (eval_affine_gej_product true size y (point_mul_words (square_words zi) zi) m3 br ba b3
   Size Max BY BZI3 RA R3 A3 RF3 AY3 AF3 Z33 F33)
  as (mf & C4 & RYF & AYF & Z3F & RFF & AFF & F3F & VY & BYO & Frame4).
 assert (RXF:fe_at mf br 0 (words5 (ge_zinv_x_words x zi))).
 { eapply curve_keep_field_range;[reflexivity|exact RX3|exact Frame4|].
   intros pos Range;repeat split;try congruence;[right;left;cbn [curve_square_offset];lia|left;congruence]. }
 assert (AXF:fe_at mf ba 0 (words5 x)).
 { eapply curve_keep_field_range;[reflexivity|exact AX3|exact Frame4|].
   intros pos Range;repeat split;try congruence;[left;congruence|right;left;cbn [curve_square_offset];lia]. }
 assert (FactorF:fe_at mf bf (ge_zinv_factor_offset point) (words5 zi)) by
  (eapply field_at_lframe;[exact Factor3|exact Frame4|];intros;repeat split;try congruence;left;congruence).
 assert (FFF:Mem.range_perm mf bf 0 (ge_zinv_factor_size point) Cur Freeable) by
  (eapply curve_keep_free;[exact FactorSize|exact FF3|exact Frame4|];intros;repeat split;try congruence;left;congruence).
 assert (F2F:Mem.range_perm mf b2 0 40 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact F23|exact Frame4|];intros;repeat split;try congruence;left;congruence).
 exists mf;split.
 - unfold ge_zinv_arithmetic.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
   + unfold ge_zinv_square_statement;run_ge_call C1;args_square ZI.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le).
     * unfold ge_zinv_cube_statement;run_ge_call C2;args_cube ZI.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le).
       -- unfold ge_zinv_product_statement;run_ge_call C3;args_product false R A.
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
          ++ unfold ge_zinv_product_statement;run_ge_call C4;args_product true R A.
          ++ constructor.
 - split;[exact RXF|];split;[exact RYF|];split;[exact AXF|];split;[exact AYF|];split;[exact FactorF|];
   split;[exact RFF|];split;[exact AFF|];split;[exact FFF|];split;[exact F2F|];split;[exact F3F|];
   split;[exact BXO|];split;[exact BYO|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact Frame1|].
     intros b pos (N2 & N3 & NF & NR & NA) Valid;split;assumption.
   + eapply lframe_trans.
     * eapply lframe_implies;[exact Frame2|].
       intros b pos (N2 & N3 & NF & NR & NA) Valid;repeat split;assumption.
     * eapply lframe_trans.
       -- eapply lframe_implies;[exact Frame3|].
          intros b pos (N2 & N3 & NF & NR & NA) Valid;cbn [curve_square_offset];
           split;[exact N2|];split;
           [destruct NR as [NR|[NR|NR]]|destruct NA as [NA|[NA|NA]]];intuition lia.
       -- eapply lframe_implies;[exact Frame4|].
          intros b pos (N2 & N3 & NF & NR & NA) Valid;cbn [curve_square_offset];
           split;[exact N3|];split;
           [destruct NR as [NR|[NR|NR]]|destruct NA as [NA|[NA|NA]]];intuition lia.
Qed.
