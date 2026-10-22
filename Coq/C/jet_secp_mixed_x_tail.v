(** Original X construction and T += X, with bounds for the following Y
    multiplication. The input point X need not be initialized. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
  C.jet_secp_square_numeric C.jet_secp_square_point_x C.jet_secp_point_field_add C.jet_secp_point_write_run
  C.jet_secp_field_add_scaled C.jet_secp_field_sum_bounds C.jet_secp_field_mul_small
  C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_curve_statements
  C.jet_secp_double_statements C.jet_secp_double_coordinate_numeric C.jet_secp_statement_prefix C.jet_secp_mixed_products.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words.

Definition mixed_x_words i g t := field_sum_words (field_sum_words (field_sum_words (square_words i) g) t) t.
Definition mixed_tx_words i g t := field_sum_words t (mixed_x_words i g t).
Definition mixed_x_square := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
  [double_point_address _r _x;curve_local_address _i].
Definition mixed_x_add (g : bool) := curve_call _secp256k1_fe_add f_secp256k1_fe_add None
  [double_point_address _r _x;curve_local_address (if g then _h3 else _t)].
Definition mixed_t_add := curve_call _secp256k1_fe_add f_secp256k1_fe_add None
  [curve_local_address _t;double_point_address _r _x].
Definition mixed_x_statements := [mixed_x_square;mixed_x_add true;mixed_x_add false;mixed_x_add false;mixed_t_add].
Definition mixed_after_x := match mixed_after_products with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ rest)))) => rest | _ => Sskip end.
Definition mixed_x_frame (bp bi bg bt bx : block) (pos : Z) :=
  bx<>bi /\ bx<>bg /\ bx<>bt /\ (bx<>bp \/ pos<0 \/ 40<=pos).
Lemma mixed_x_source : mixed_after_products=statement_sequence mixed_x_statements mixed_after_x.
Proof. reflexivity. Qed.

Lemma mixed_x_bounds i g t : square_input_bounds i -> mul_small_input_bounds g -> mul_small_input_bounds t ->
  field_scaled_bounds 4 (mixed_x_words i g t) /\ field_scaled_bounds 5 (mixed_tx_words i g t) /\
  radix_value (mixed_x_words i g t)=radix_value (square_words i)+radix_value g+2*radix_value t /\
  radix_value (mixed_tx_words i g t)=radix_value (square_words i)+radix_value g+3*radix_value t.
Proof.
  intros BI BG BT.
  pose proof (field_tight_scaled _ (double_square_tight i BI)) as BS.
  pose proof (field_tight_scaled g BG) as GS;pose proof (field_tight_scaled t BT) as TS.
  pose proof (field_sum_scaled_bounds 1 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) BS GS) as B1.
  pose proof (field_sum_scaled_bounds 2 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) B1 TS) as B2.
  pose proof (field_sum_scaled_bounds 3 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) B2 TS) as BX.
  pose proof (field_sum_scaled_bounds 1 4 _ _ ltac:(lia) ltac:(lia) ltac:(lia) TS BX) as BTT.
  assert (VX : radix_value (mixed_x_words i g t)=radix_value (square_words i)+radix_value g+2*radix_value t).
  { unfold mixed_x_words;rewrite (field_sum_exact_value _ _
      (field_sum_scaled_no_overflow 3 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) B2 TS)),
      (field_sum_exact_value _ _ (field_sum_scaled_no_overflow 2 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) B1 TS)),
      (field_sum_exact_value _ _ (field_sum_scaled_no_overflow 1 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) BS GS));ring. }
  split;[exact BX|];split;[exact BTT|];split;[exact VX|].
  unfold mixed_tx_words;rewrite (field_sum_exact_value t (mixed_x_words i g t)
    (field_sum_scaled_no_overflow 1 4 t (mixed_x_words i g t) ltac:(lia) ltac:(lia) ltac:(lia) TS BX)),VX;ring.
Qed.

Local Ltac keep_x_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac keep_x_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac square_outside := intro pos;unfold square_two_ranges;intros [[HE _]|[HE _]];congruence.
Local Ltac original_pure := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).

Theorem exec_mixed_x_tail e le m bp bi bg bt i g t :
  le!_r=Some (Vptr bp Ptrofs.zero) -> e!_i=Some (bi,curve_fe_type) ->
  e!_h3=Some (bg,curve_fe_type) -> e!_t=Some (bt,curve_fe_type) ->
  e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_add=None ->
  bp<>bi -> bp<>bg -> bp<>bt -> bi<>bg -> bi<>bt -> bg<>bt ->
  square_input_bounds i -> mul_small_input_bounds g -> mul_small_input_bounds t ->
  fe_at m bi 0 (words5 i) -> fe_at m bg 0 (words5 g) -> fe_at m bt 0 (words5 t) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  Mem.range_perm m bg 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_x_statements Sskip) E0 le mf Out_normal /\
  fe_at mf bp 0 (words5 (mixed_x_words i g t)) /\ fe_at mf bt 0 (words5 (mixed_tx_words i g t)) /\
  fe_at mf bi 0 (words5 i) /\ fe_at mf bg 0 (words5 g) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  Mem.range_perm mf bg 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  field_scaled_bounds 4 (mixed_x_words i g t) /\ field_scaled_bounds 5 (mixed_tx_words i g t) /\
  radix_value (mixed_x_words i g t)=radix_value (square_words i)+radix_value g+2*radix_value t /\
  radix_value (mixed_tx_words i g t)=radix_value (square_words i)+radix_value g+3*radix_value t /\
  lframe (mixed_x_frame bp bi bg bt) m mf.
Proof.
  intros HR EI EG ET EQ EA SPI SPG SPT SIG SIT SGT BI BG BT I G T PF IF GF TF.
  destruct (eval_square_point_x i m bp bi BI PF I IF SPI)
    as (m0 & CS & X0 & PF0 & I0 & IF0 & VS & BS & TS & FS).
  assert (G0 : fe_at m0 bg 0 (words5 g)).
  { eapply field_at_lframe;[exact G|exact FS|square_outside]. }
  assert (T0 : fe_at m0 bt 0 (words5 t)).
  { eapply field_at_lframe;[exact T|exact FS|square_outside]. }
  assert (GF0 : Mem.range_perm m0 bg 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact GF|exact FS|square_outside]. }
  assert (TF0 : Mem.range_perm m0 bt 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact TF|exact FS|square_outside]. }
  destruct (eval_point_field_add true PointX (square_words i) g m0 bp bg SPG X0 PF0 G0 GF0)
    as (m1 & C1 & X1 & G1 & PF1 & GF1 & F1).
  assert (T1 : fe_at m1 bt 0 (words5 t)) by (keep_x_field T0 F1).
  assert (TF1 : Mem.range_perm m1 bt 0 40 Cur Freeable) by (keep_x_free TF0 F1).
  destruct (eval_point_field_add true PointX (field_sum_words (square_words i) g) t m1 bp bt SPT X1 PF1 T1 TF1)
    as (m2 & C2 & X2 & T2 & PF2 & TF2 & F2).
  destruct (eval_point_field_add true PointX (field_sum_words (field_sum_words (square_words i) g) t) t m2 bp bt SPT X2 PF2 T2 TF2)
    as (m3 & C3 & X3 & T3 & PF3 & TF3 & F3).
  destruct (eval_point_field_add false PointX (mixed_x_words i g t) t m3 bp bt SPT X3 PF3 T3 TF3)
    as (mf & C4 & XO & TO & PFO & TFO & F4).
  pose proof (lframe_trans _ m1 m2 m3 F2 F3) as F23.
  pose proof (lframe_trans _ m1 m3 mf F23 F4) as F234.
  assert (GO : fe_at mf bg 0 (words5 g)) by (keep_x_field G1 F234).
  assert (GFO : Mem.range_perm mf bg 0 40 Cur Freeable) by (keep_x_free GF1 F234).
  assert (FI : lframe (fun bx pos=>bx<>bg /\ bx<>bt /\ (bx<>bp \/ pos<0 \/ 40<=pos)) m0 mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact F1|];intros bx pos (NG & NT & NP) HV;split;assumption.
    - eapply lframe_implies;[exact F234|];intros bx pos (NG & NT & NP) HV;split;assumption. }
  assert (IO : fe_at mf bi 0 (words5 i)) by (keep_x_field I0 FI).
  assert (IFO : Mem.range_perm mf bi 0 40 Cur Freeable) by (keep_x_free IF0 FI).
  assert (Frame : lframe (mixed_x_frame bp bi bg bt) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FS|];intros bx pos (NI & NG & NT & NP) HV [[HE HP]|[HE HP]];[|contradiction].
      subst bx;destruct NP as [NP|[NP|NP]];[contradiction|lia|lia].
    - eapply lframe_implies;[exact FI|];intros bx pos (NI & NG & NT & NP) HV;repeat split;assumption. }
  destruct (mixed_x_bounds i g t BI BG BT) as (BX & BTT & VX & VT).
  exists mf;split.
  - unfold mixed_x_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m0) (le1:=le).
    + unfold mixed_x_square;eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero;Vptr bi Ptrofs.zero]) (v:=Vundef).
      * original_pure.
      * exact EQ.
      * eapply eval_Econs with (v1:=Vptr bp Ptrofs.zero);
          [apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|].
        eapply eval_Econs;[apply eval_curve_local;exact EI|reflexivity|constructor].
      * exact CS.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
      * unfold mixed_x_add;eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero;Vptr bg Ptrofs.zero]) (v:=Vundef).
        -- original_pure.
        -- exact EA.
        -- eapply eval_Econs with (v1:=Vptr bp Ptrofs.zero);
             [apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|].
           eapply eval_Econs;[apply eval_curve_local;exact EG|reflexivity|constructor].
        -- exact C1.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le).
        -- unfold mixed_x_add;eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero;Vptr bt Ptrofs.zero]) (v:=Vundef).
           ++ original_pure.
           ++ exact EA.
           ++ eapply eval_Econs with (v1:=Vptr bp Ptrofs.zero);
                [apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|].
              eapply eval_Econs;[apply eval_curve_local;exact ET|reflexivity|constructor].
           ++ exact C2.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le).
           ++ unfold mixed_x_add;eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero;Vptr bt Ptrofs.zero]) (v:=Vundef).
              ** original_pure.
              ** exact EA.
              ** eapply eval_Econs with (v1:=Vptr bp Ptrofs.zero);
                   [apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|].
                 eapply eval_Econs;[apply eval_curve_local;exact ET|reflexivity|constructor].
              ** exact C3.
           ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
              ** unfold mixed_t_add;eapply exec_curve_call with (vargs:=[Vptr bt Ptrofs.zero;Vptr bp Ptrofs.zero]) (v:=Vundef).
                 --- original_pure.
                 --- exact EA.
                 --- eapply eval_Econs;[apply eval_curve_local;exact ET|reflexivity|].
                     eapply eval_Econs with (v1:=Vptr bp Ptrofs.zero);
                       [apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|constructor].
                 --- exact C4.
              ** apply exec_Sskip.
  - repeat (first [assumption|split]).
Qed.
