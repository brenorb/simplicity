(** Original H2 negation and H3/T products, from initial owned private fields.
    The multiplication destinations need no initialized contents. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_field_negate_separate
  C.jet_secp_field_negate_owned C.jet_secp_field_product_owned C.jet_secp_curve_frame
  C.jet_secp_field_read_preservation C.jet_secp_curve_statements C.jet_secp_statement_prefix
  C.jet_secp_mixed_nonzero_start.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words negate_sep_words.

Definition mixed_h2_negate := curve_call _secp256k1_fe_negate f_secp256k1_fe_negate None
  [curve_local_address _h2;curve_local_address _h2;Econst_int Int.one tint].
Definition mixed_h3_mul := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [curve_local_address _h3;curve_local_address _h2;curve_local_address _h].
Definition mixed_t_mul := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [curve_local_address _t;curve_local_address _u1;curve_local_address _h2].
Definition mixed_product_statements := [mixed_h2_negate;mixed_h3_mul;mixed_t_mul].
Definition mixed_after_products := match mixed_after_h_square with
  | Ssequence _ (Ssequence _ (Ssequence _ rest)) => rest | _ => Sskip end.
Definition mixed_product_frame (b2 b3 bt bh bu bx : block) (_ : Z) :=
  bx<>b2 /\ bx<>b3 /\ bx<>bt /\ bx<>bh /\ bx<>bu.
Lemma mixed_products_source : mixed_after_h_square=
  statement_sequence mixed_product_statements mixed_after_products.
Proof. reflexivity. Qed.

Local Ltac separate_product_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_product_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac keep_product_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac original_pure := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).

Theorem exec_mixed_products e le m b2 b3 bt bh bu q h u :
  e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) -> e!_t=Some (bt,curve_fe_type) ->
  e!_h=Some (bh,curve_fe_type) -> e!_u1=Some (bu,curve_fe_type) ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_mul=None -> NoDup [b2;b3;bt;bh;bu] ->
  mul_small_input_bounds q -> square_input_bounds h -> square_input_bounds u ->
  fe_at m b2 0 (words5 q) -> fe_at m bh 0 (words5 h) -> fe_at m bu 0 (words5 u) ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bu 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_product_statements Sskip) E0 le mf Out_normal /\
  fe_at mf b2 0 (words5 (negate_sep_words q)) /\
  fe_at mf b3 0 (words5 (point_mul_words (negate_sep_words q) h)) /\
  fe_at mf bt 0 (words5 (point_mul_words u (negate_sep_words q))) /\
  fe_at mf bh 0 (words5 h) /\ fe_at mf bu 0 (words5 u) /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bu 0 40 Cur Freeable /\
  radix_value (negate_sep_words q)=4*feP-radix_value q /\ square_input_bounds (negate_sep_words q) /\
  radix_value (point_mul_words (negate_sep_words q) h) mod feP=(radix_value (negate_sep_words q)*radix_value h) mod feP /\
  radix_value (point_mul_words u (negate_sep_words q)) mod feP=(radix_value u*radix_value (negate_sep_words q)) mod feP /\
  mul_small_input_bounds (point_mul_words (negate_sep_words q) h) /\
  mul_small_input_bounds (point_mul_words u (negate_sep_words q)) /\ lframe (mixed_product_frame b2 b3 bt bh bu) m mf.
Proof.
  intros E2 E3 ET EH EU EN EM Sep BQ BH BU Q H U F2 F3 FT FH FU.
  separate_product_blocks Sep.
  destruct (eval_inplace_negate_tight_owned q m b2 BQ Q F2)
    as (mn & CN & N & F2N & ValN & BoundN & FN).
  assert (HN : fe_at mn bh 0 (words5 h)) by (keep_product_field H FN).
  assert (UN : fe_at mn bu 0 (words5 u)) by (keep_product_field U FN).
  assert (F3N : Mem.range_perm mn b3 0 40 Cur Freeable) by (keep_product_free F3 FN).
  assert (FTN : Mem.range_perm mn bt 0 40 Cur Freeable) by (keep_product_free FT FN).
  assert (FHN : Mem.range_perm mn bh 0 40 Cur Freeable) by (keep_product_free FH FN).
  assert (FUN : Mem.range_perm mn bu 0 40 Cur Freeable) by (keep_product_free FU FN).
  destruct (eval_field_product_owned (negate_sep_words q) h mn b3 b2 bh BoundN BH
    ltac:(congruence) ltac:(congruence) ltac:(congruence) F3N N F2N HN FHN)
    as (m3 & C3 & H3 & NS3 & H3S & F33 & F23 & FH3 & Val3 & Bound3 & Frame3).
  assert (U3 : fe_at m3 bu 0 (words5 u)) by (keep_product_field UN Frame3).
  assert (FT3 : Mem.range_perm m3 bt 0 40 Cur Freeable) by (keep_product_free FTN Frame3).
  assert (FU3 : Mem.range_perm m3 bu 0 40 Cur Freeable) by (keep_product_free FUN Frame3).
  destruct (eval_field_product_owned u (negate_sep_words q) m3 bt bu b2 BU BoundN
    ltac:(congruence) ltac:(congruence) ltac:(congruence) FT3 U3 FU3 NS3 F23)
    as (mf & CT & TO & UO & NO & FTO & FUO & F2O & ValT & BoundT & FrameT).
  assert (H3O : fe_at mf b3 0 (words5 (point_mul_words (negate_sep_words q) h))) by (keep_product_field H3 FrameT).
  assert (HO : fe_at mf bh 0 (words5 h)) by (keep_product_field H3S FrameT).
  assert (F3O : Mem.range_perm mf b3 0 40 Cur Freeable) by (keep_product_free F33 FrameT).
  assert (FHO : Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_product_free FH3 FrameT).
  assert (Frame : lframe (mixed_product_frame b2 b3 bt bh bu) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FN|];intros bx pos (N2 & N3 & NT & NH & NU) HV;exact N2.
    - eapply lframe_trans.
      + eapply lframe_implies;[exact Frame3|];intros bx pos (N2 & N3 & NT & NH & NU) HV;repeat split;assumption.
      + eapply lframe_implies;[exact FrameT|];intros bx pos (N2 & N3 & NT & NH & NU) HV;repeat split;assumption. }
  exists mf;split.
  - unfold mixed_product_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le).
    + unfold mixed_h2_negate;eapply exec_curve_call with (vargs:=[Vptr b2 Ptrofs.zero;Vptr b2 Ptrofs.zero;Vint Int.one]) (v:=Vundef).
      * original_pure.
      * exact EN.
      * eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|].
        eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|].
        eapply eval_Econs;[constructor|reflexivity|constructor].
      * exact CN.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le).
      * unfold mixed_h3_mul;eapply exec_curve_call with (vargs:=[Vptr b3 Ptrofs.zero;Vptr b2 Ptrofs.zero;Vptr bh Ptrofs.zero]) (v:=Vundef).
        -- original_pure.
        -- exact EM.
        -- eapply eval_Econs;[apply eval_curve_local;exact E3|reflexivity|].
           eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|].
           eapply eval_Econs;[apply eval_curve_local;exact EH|reflexivity|constructor].
        -- exact C3.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
        -- unfold mixed_t_mul;eapply exec_curve_call with (vargs:=[Vptr bt Ptrofs.zero;Vptr bu Ptrofs.zero;Vptr b2 Ptrofs.zero]) (v:=Vundef).
           ++ original_pure.
           ++ exact EM.
           ++ eapply eval_Econs;[apply eval_curve_local;exact ET|reflexivity|].
              eapply eval_Econs;[apply eval_curve_local;exact EU|reflexivity|].
              eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|constructor].
           ++ exact CT.
        -- apply exec_Sskip.
  - repeat (first [assumption|split]).
Qed.
