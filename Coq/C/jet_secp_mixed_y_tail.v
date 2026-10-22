(** Last three original mixed-addition operations: Y=T*I, H3*=S1, Y+=H3.
    Derive the calls, resulting words and reusable bounds from owned storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_point_y_product C.jet_secp_field_pair_multiply
  C.jet_secp_field_add_scaled C.jet_secp_field_sum_bounds C.jet_secp_point_field_add C.jet_secp_point_write_run
  C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_curve_statements
  C.jet_secp_double_statements C.jet_secp_statement_prefix C.jet_secp_mixed_x_tail C.jet_secp_mixed_products.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words field_pair_product.

Definition mixed_y_words t i g s := field_sum_words (point_mul_words t i) (field_pair_product g s).
Definition mixed_y_mul := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [double_point_address _r _y;curve_local_address _t;curve_local_address _i].
Definition mixed_h3_s_mul := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [curve_local_address _h3;curve_local_address _h3;curve_local_address _s1].
Definition mixed_y_add := curve_call _secp256k1_fe_add f_secp256k1_fe_add None
  [double_point_address _r _y;curve_local_address _h3].
Definition mixed_y_prefix := [mixed_y_mul;mixed_h3_s_mul].
Definition mixed_y_frame (bp bt bi bg bs bx : block) (pos : Z) :=
  bx<>bt /\ bx<>bi /\ bx<>bg /\ bx<>bs /\ (bx<>bp \/ pos<40 \/ 80<=pos).
Lemma mixed_y_source : mixed_after_x=statement_sequence mixed_y_prefix mixed_y_add.
Proof. reflexivity. Qed.

Local Ltac separate_y_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_y_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac keep_y_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac original_pure := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).

Theorem exec_mixed_y_tail e le m bp bt bi bg bs t i g s :
  le!_r=Some (Vptr bp Ptrofs.zero) -> e!_t=Some (bt,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_h3=Some (bg,curve_fe_type) -> e!_s1=Some (bs,curve_fe_type) ->
  e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_add=None -> NoDup [bp;bt;bi;bg;bs] ->
  square_input_bounds t -> square_input_bounds i -> square_input_bounds g -> square_input_bounds s ->
  fe_at m bt 0 (words5 t) -> fe_at m bi 0 (words5 i) -> fe_at m bg 0 (words5 g) -> fe_at m bs 0 (words5 s) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m bg 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_after_x E0 le mf Out_normal /\
  fe_at mf bp 40 (words5 (mixed_y_words t i g s)) /\ fe_at mf bg 0 (words5 (field_pair_product g s)) /\
  fe_at mf bt 0 (words5 t) /\ fe_at mf bi 0 (words5 i) /\ fe_at mf bs 0 (words5 s) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bi 0 40 Cur Freeable /\ Mem.range_perm mf bg 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  field_scaled_bounds 2 (mixed_y_words t i g s) /\ mul_small_input_bounds (field_pair_product g s) /\
  radix_value (mixed_y_words t i g s)=radix_value (point_mul_words t i)+radix_value (field_pair_product g s) /\
  lframe (mixed_y_frame bp bt bi bg bs) m mf.
Proof.
  intros HR ET EI EG ES EM EA Sep BT BI BG BS T I G S PF TF IF GF SF.
  separate_y_blocks Sep.
  destruct (eval_point_y_product t i m bp bt bi BT BI ltac:(congruence) ltac:(congruence) ltac:(congruence) PF T TF I IF)
    as (m1 & C1 & Y1 & T1 & I1 & PF1 & TF1 & IF1 & VY & BY & F1).
  assert (G1 : fe_at m1 bg 0 (words5 g)) by (keep_y_field G F1).
  assert (S1 : fe_at m1 bs 0 (words5 s)) by (keep_y_field S F1).
  assert (GF1 : Mem.range_perm m1 bg 0 40 Cur Freeable) by (keep_y_free GF F1).
  assert (SF1 : Mem.range_perm m1 bs 0 40 Cur Freeable) by (keep_y_free SF F1).
  destruct (eval_field_pair_multiply g s m1 bg bs BG BS ltac:(congruence) G1 S1 GF1 SF1)
    as (m2 & C2 & G2 & S2 & GF2 & SF2 & VG & BLG & BTG & F2).
  assert (Y2 : fe_at m2 bp 40 (words5 (point_mul_words t i))) by (keep_y_field Y1 F2).
  assert (PF2 : Mem.range_perm m2 bp 0 128 Cur Freeable) by (keep_y_free PF1 F2).
  assert (T2 : fe_at m2 bt 0 (words5 t)) by (keep_y_field T1 F2).
  assert (I2 : fe_at m2 bi 0 (words5 i)) by (keep_y_field I1 F2).
  assert (TF2 : Mem.range_perm m2 bt 0 40 Cur Freeable) by (keep_y_free TF1 F2).
  assert (IF2 : Mem.range_perm m2 bi 0 40 Cur Freeable) by (keep_y_free IF1 F2).
  destruct (eval_point_field_add true PointY (point_mul_words t i) (field_pair_product g s) m2 bp bg
    ltac:(congruence) Y2 PF2 G2 GF2)
    as (mf & C3 & YO & GO & PFO & GFO & F3).
  assert (TO : fe_at mf bt 0 (words5 t)) by (keep_y_field T2 F3).
  assert (IO : fe_at mf bi 0 (words5 i)) by (keep_y_field I2 F3).
  assert (SO : fe_at mf bs 0 (words5 s)) by (keep_y_field S2 F3).
  assert (TFO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_y_free TF2 F3).
  assert (IFO : Mem.range_perm mf bi 0 40 Cur Freeable) by (keep_y_free IF2 F3).
  assert (SFO : Mem.range_perm mf bs 0 40 Cur Freeable) by (keep_y_free SF2 F3).
  assert (BGout : mul_small_input_bounds (field_pair_product g s)).
  { intros n HN;exact (proj2 (BTG n HN)). }
  pose proof (field_tight_scaled _ BY) as BY1;pose proof (field_tight_scaled _ BGout) as BG1.
  pose proof (field_sum_scaled_bounds 1 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) BY1 BG1) as BoundY.
  assert (ValY : radix_value (mixed_y_words t i g s)=radix_value (point_mul_words t i)+radix_value (field_pair_product g s)).
  { unfold mixed_y_words;apply field_sum_exact_value;exact (field_sum_scaled_no_overflow 1 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) BY1 BG1). }
  assert (Frame : lframe (mixed_y_frame bp bt bi bg bs) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact F1|];intros bx pos (NT & NI & NG & NS & NP) HV;repeat split;assumption.
    - eapply lframe_trans.
      + eapply lframe_implies;[exact F2|];intros bx pos (NT & NI & NG & NS & NP) HV;split;assumption.
      + eapply lframe_implies;[exact F3|];intros bx pos (NT & NI & NG & NS & NP) HV;split;assumption. }
  exists mf;split.
  - rewrite mixed_y_source;unfold mixed_y_prefix;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
    + unfold mixed_y_mul;eapply exec_curve_call with (vargs:=[Vptr bp (Ptrofs.repr 40);Vptr bt Ptrofs.zero;Vptr bi Ptrofs.zero]) (v:=Vundef).
      * original_pure.
      * exact EM.
      * eapply eval_Econs with (v1:=Vptr bp (Ptrofs.repr 40));
          [apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|].
        eapply eval_Econs;[apply eval_curve_local;exact ET|reflexivity|].
        eapply eval_Econs;[apply eval_curve_local;exact EI|reflexivity|constructor].
      * exact C1.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le).
      * unfold mixed_h3_s_mul;eapply exec_curve_call with (vargs:=[Vptr bg Ptrofs.zero;Vptr bg Ptrofs.zero;Vptr bs Ptrofs.zero]) (v:=Vundef).
        -- original_pure.
        -- exact EM.
        -- eapply eval_Econs;[apply eval_curve_local;exact EG|reflexivity|].
           eapply eval_Econs;[apply eval_curve_local;exact EG|reflexivity|].
           eapply eval_Econs;[apply eval_curve_local;exact ES|reflexivity|constructor].
        -- exact C2.
      * unfold mixed_y_add;eapply exec_curve_call with (vargs:=[Vptr bp (Ptrofs.repr 40);Vptr bg Ptrofs.zero]) (v:=Vundef).
        -- original_pure.
        -- exact EA.
        -- eapply eval_Econs with (v1:=Vptr bp (Ptrofs.repr 40));
             [apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|].
           eapply eval_Econs;[apply eval_curve_local;exact EG|reflexivity|constructor].
        -- exact C3.
  - repeat (first [assumption|split]).
Qed.

Definition mixed_xy_frame (bp bi bg bt bs bx : block) (pos : Z) :=
  bx<>bi /\ bx<>bg /\ bx<>bt /\ bx<>bs /\ (bx<>bp \/ pos<0 \/ 80<=pos).

Theorem exec_mixed_xy_tail e le m bp bi bg bt bs i g t s :
  le!_r=Some (Vptr bp Ptrofs.zero) -> e!_i=Some (bi,curve_fe_type) -> e!_h3=Some (bg,curve_fe_type) ->
  e!_t=Some (bt,curve_fe_type) -> e!_s1=Some (bs,curve_fe_type) ->
  e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_add=None -> NoDup [bp;bt;bi;bg;bs] ->
  square_input_bounds i -> mul_small_input_bounds g -> mul_small_input_bounds t -> square_input_bounds s ->
  fe_at m bi 0 (words5 i) -> fe_at m bg 0 (words5 g) -> fe_at m bt 0 (words5 t) -> fe_at m bs 0 (words5 s) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  Mem.range_perm m bg 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_after_products E0 le mf Out_normal /\
  fe_at mf bp 0 (words5 (mixed_x_words i g t)) /\
  fe_at mf bp 40 (words5 (mixed_y_words (mixed_tx_words i g t) i g s)) /\
  fe_at mf bt 0 (words5 (mixed_tx_words i g t)) /\ fe_at mf bg 0 (words5 (field_pair_product g s)) /\
  fe_at mf bi 0 (words5 i) /\ fe_at mf bs 0 (words5 s) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  Mem.range_perm mf bg 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  field_scaled_bounds 4 (mixed_x_words i g t) /\
  field_scaled_bounds 2 (mixed_y_words (mixed_tx_words i g t) i g s) /\
  field_scaled_bounds 5 (mixed_tx_words i g t) /\ lframe (mixed_xy_frame bp bi bg bt bs) m mf.
Proof.
  intros HR EI EG ET ES EQ EM EA Sep BI BG BT BS I G T S PF IF GF TF SF.
  pose proof Sep as Sep0;separate_y_blocks Sep.
  destruct (exec_mixed_x_tail e le m bp bi bg bt i g t HR EI EG ET EQ EA
    ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)
    BI BG BT I G T PF IF GF TF)
    as (mx & CX & XX & TX & IX & GX & PFX & IFX & GFX & TFX & BoundX & BoundT & ValX & ValT & FX).
  assert (SX : fe_at mx bs 0 (words5 s)) by (keep_y_field S FX).
  assert (SFX : Mem.range_perm mx bs 0 40 Cur Freeable) by (keep_y_free SF FX).
  destruct (exec_mixed_y_tail e le mx bp bt bi bg bs (mixed_tx_words i g t) i g s
    HR ET EI EG ES EM EA Sep0 (field_scaled_loose 5 _ ltac:(lia) BoundT) BI
    (field_scaled_loose 1 _ ltac:(lia) (field_tight_scaled _ BG)) BS TX IX GX SX PFX TFX IFX GFX SFX)
    as (mf & CY & YO & GO & TO & IO & SO & PFO & TFO & IFO & GFO & SFO & BoundY & BoundG & ValY & FY).
  assert (XO : fe_at mf bp 0 (words5 (mixed_x_words i g t))).
  { eapply curve_keep_field_range;[reflexivity|exact XX|exact FY|].
    intros pos HP;unfold mixed_y_frame;repeat split;try congruence;right;left;lia. }
  assert (Frame : lframe (mixed_xy_frame bp bi bg bt bs) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FX|];intros bx pos (NI & NG & NT & NS & NP) HV.
      unfold mixed_x_frame;split;[exact NI|];split;[exact NG|];split;[exact NT|].
      destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;exact NP|right;right;lia].
    - eapply lframe_implies;[exact FY|];intros bx pos (NI & NG & NT & NS & NP) HV.
      unfold mixed_y_frame;split;[exact NT|];split;[exact NI|];split;[exact NG|];split;[exact NS|].
      destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;lia|right;right;exact NP]. }
  exists mf;split.
  - rewrite mixed_x_source;eapply exec_statement_prefix_then_last;[exact CX|exact CY].
  - repeat (first [assumption|split]).
Qed.
