(** Shared original mixed-addition body with loose X/Y support. Doubling
    uses the raw point, while nonzero arithmetic uses actual normalized U1/S1.
    The original positioned-X definitions and contracts remain unchanged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix
  C.jet_secp_mixed_preparation C.jet_secp_mixed_finite_prefix C.jet_secp_mixed_finite_return
  C.jet_secp_mixed_zero_return C.jet_secp_mixed_nonzero_tail C.jet_secp_double_all_calls C.jet_secp_double_coordinate_numeric.
Require Import C.jet_secp_mixed_preparation_loose C.jet_secp_mixed_finite_body C.jet_secp_mixed_finite_loose
 C.jet_secp_mixed_return_loose C.jet_secp_field_weak_loose.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words weak_loose_words.

Definition mixed_loose_finite_x_words x y z u v :=
  if Z.eqb (radix_value (mixed_h_words x z u) mod feP) 0
  then mixed_zero_words (mixed_i_words (weak_loose_words y) z v) (double_output_x_words x y)
  else mixed_nonzero_x_words (mixed_h_words x z u) (mixed_i_words (weak_loose_words y) z v) x.
Definition mixed_loose_finite_y_words x y z u v :=
  if Z.eqb (radix_value (mixed_h_words x z u) mod feP) 0
  then mixed_zero_words (mixed_i_words (weak_loose_words y) z v) (double_output_y_words x y)
  else mixed_nonzero_y_words (mixed_h_words x z u) (mixed_i_words (weak_loose_words y) z v) x (weak_loose_words y).
Definition mixed_loose_finite_z_words x y z u v :=
  if Z.eqb (radix_value (mixed_h_words x z u) mod feP) 0
  then mixed_zero_words (mixed_i_words (weak_loose_words y) z v) (double_output_z_words y z)
  else point_mul_words z (mixed_h_words x z u).
Definition mixed_loose_finite_flag x y z u v :=
  if Z.eqb (radix_value (mixed_h_words x z u) mod feP) 0
  then mixed_zero_flag (mixed_i_words (weak_loose_words y) z v) y z else Int.zero.
Definition mixed_loose_finite_body_temps le x y z u v :=
  if Z.eqb (radix_value (mixed_h_words x z u) mod feP) 0
  then mixed_zero_return_temps (mixed_preparation_temps le) (mixed_i_words (weak_loose_words y) z v)
  else PTree.set _t'2 (Vint Int.zero) (mixed_preparation_temps le).
Local Ltac separate_finite_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac finite_separated :=
  repeat rewrite NoDup_cons_iff;cbn [In];repeat split;intuition congruence.
Local Ltac keep_finite_owned HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac outside_preparation :=
  unfold mixed_finite_difference_frame,mixed_prepare_frame;
    repeat split;try (left;congruence);congruence.

Definition mixed_mode_finite_x_words loose x y z u v :=
  if Z.eqb (radix_value (mixed_h_words (mixed_x_words loose x) z u) mod feP) 0
  then mixed_zero_words (mixed_i_words (weak_loose_words y) z v) (double_output_x_words x y)
  else mixed_nonzero_x_words (mixed_h_words (mixed_x_words loose x) z u)
    (mixed_i_words (weak_loose_words y) z v) (mixed_x_words loose x).
Definition mixed_mode_finite_y_words loose x y z u v :=
  if Z.eqb (radix_value (mixed_h_words (mixed_x_words loose x) z u) mod feP) 0
  then mixed_zero_words (mixed_i_words (weak_loose_words y) z v) (double_output_y_words x y)
  else mixed_nonzero_y_words (mixed_h_words (mixed_x_words loose x) z u)
    (mixed_i_words (weak_loose_words y) z v) (mixed_x_words loose x) (weak_loose_words y).
Definition mixed_mode_finite_z_words loose x y z u v :=
  if Z.eqb (radix_value (mixed_h_words (mixed_x_words loose x) z u) mod feP) 0
  then mixed_zero_words (mixed_i_words (weak_loose_words y) z v) (double_output_z_words y z)
  else point_mul_words z (mixed_h_words (mixed_x_words loose x) z u).
Definition mixed_mode_finite_flag loose x y z u v :=
  if Z.eqb (radix_value (mixed_h_words (mixed_x_words loose x) z u) mod feP) 0
  then mixed_zero_flag (mixed_i_words (weak_loose_words y) z v) y z else Int.zero.
Definition mixed_mode_finite_body_temps loose le x y z u v :=
  if Z.eqb (radix_value (mixed_h_words (mixed_x_words loose x) z u) mod feP) 0
  then mixed_zero_return_temps (mixed_preparation_temps le) (mixed_i_words (weak_loose_words y) z v)
  else PTree.set _t'2 (Vint Int.zero) (mixed_preparation_temps le).

Theorem exec_mixed_finite_body_mode (loose:bool) e le m bp ba bu bv bs bt bz bh bi b2 b3 bk x y z u v :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) -> e!_t=Some (bk,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None ->
  NoDup [bp;ba;bu;bv;bs;bt;bz;bh;bi;b2;b3;bk] ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
  mixed_x_body_bound loose x ->
  square_input_bounds y ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bz 0 40 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> Mem.range_perm m bk 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (mixed_mode_finite_body_temps loose le x y z u v) mf (mixed_finite_body_out (mixed_x_words loose x) z u) /\
  fe_at mf bp 0 (words5 (mixed_mode_finite_x_words loose x y z u v)) /\
  fe_at mf bp 40 (words5 (mixed_mode_finite_y_words loose x y z u v)) /\
  fe_at mf bp 80 (words5 (mixed_mode_finite_z_words loose x y z u v)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_mode_finite_flag loose x y z u v)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\ Mem.range_perm mf bk 0 40 Cur Freeable /\
  square_input_bounds (mixed_mode_finite_x_words loose x y z u v) /\ square_input_bounds (mixed_mode_finite_y_words loose x y z u v) /\
  square_input_bounds (mixed_mode_finite_z_words loose x y z u v) /\
  lframe (mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk) m mf.
Proof.
  intros HA HB HR HN EU EV ES ET EZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF Sep FlagA FlagB BX BY BZ BU BV
    X Y Z U V PF AF UF VF SF TF ZF HF IF F2 F3 FK.
  destruct (mixed_x_body_inputs loose x BX) as [PrepXBound RawXBound].
  separate_finite_blocks Sep.
  assert (SepP : NoDup [bh;bi;bp;ba;bu;bv;bs;bt;bz]) by finite_separated.
  assert (SepN : NoDup [bp;bh;b2;b3;bk;bu;bi;bs]) by finite_separated.
  unfold mixed_mode_finite_body_temps,mixed_finite_body_out,mixed_mode_finite_x_words,mixed_mode_finite_y_words,
    mixed_mode_finite_z_words,mixed_mode_finite_flag.
  destruct (Z.eqb (radix_value (mixed_h_words (mixed_x_words loose x) z u) mod feP) 0) eqn:HC.
  - apply Z.eqb_eq in HC.
    destruct (exec_mixed_finite_zero_body_mode loose e le m bp ba bu bv bs bt bz bh bi x y z u v
      HA HB HR HN EU EV ES ET EZ EH EI EW EM EQ EN EA E0N ED EF SepP FlagA FlagB BX BY BZ BU BV HC
      X Y Z U V PF AF UF VF SF TF ZF HF IF)
      as (mf & CB & XO & YO & ZO & FlagO & PFO & AFO & UFO & VFO & SFO & TFO & ZFO & HFO & IFO & BXO & BYO & BZO & FB).
    assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_finite_owned F2 FB).
    assert (F3O : Mem.range_perm mf b3 0 40 Cur Freeable) by (keep_finite_owned F3 FB).
    assert (FKO : Mem.range_perm mf bk 0 40 Cur Freeable) by (keep_finite_owned FK FB).
    assert (Frame : lframe (mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk) m mf).
    { eapply lframe_implies;[exact FB|];intros bx pos (FF & N2 & N3 & NK) HV;exact FF. }
    exists mf;repeat (first [assumption|split]).
  - apply Z.eqb_neq in HC.
    destruct (exec_mixed_finite_difference_mode loose e le m bp ba bu bv bs bt bz bh bi x y z u v
      HA HB EU EV ES ET EZ EH EI EW EM EQ EN EA SepP FlagA FlagB PrepXBound ltac:(intros j HJ;pose proof (square_input56 y BY j HJ);lia) BZ BU BV X Y Z U V PF AF UF VF SF TF ZF HF IF)
      as (mp & CP & XP & YP & ZP & UP & VP & U1 & U2 & S1 & S2 & Z12 & H & I & FlagAP & FlagBP &
        PFP & AFP & UFP & VFP & SFP & TFP & ZFP & HFP & IFP & TightX & TightY & TightU & TightS & ValH & ValI & BoundH & BoundI & FP).
    assert (F2P : Mem.range_perm mp b2 0 40 Cur Freeable).
    { eapply curve_keep_free;[lia|exact F2|exact FP|];intro pos;outside_preparation. }
    assert (F3P : Mem.range_perm mp b3 0 40 Cur Freeable).
    { eapply curve_keep_free;[lia|exact F3|exact FP|];intro pos;outside_preparation. }
    assert (FKP : Mem.range_perm mp bk 0 40 Cur Freeable).
    { eapply curve_keep_free;[lia|exact FK|exact FP|];intro pos;outside_preparation. }
    assert (HAP : (mixed_preparation_temps le)!_a=Some (Vptr bp Ptrofs.zero)).
    { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HA. }
    assert (HRP : (mixed_preparation_temps le)!_r=Some (Vptr bp Ptrofs.zero)).
    { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HR. }
    assert (HNP : (mixed_preparation_temps le)!_rzr=Some (Vlong Int64.zero)).
    { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HN. }
    destruct (exec_mixed_nonzero_tail e (mixed_preparation_temps le) mp bp bh b2 b3 bk bu bi bs x y z
      (mixed_h_words (mixed_x_words loose x) z u) (mixed_x_words loose x) (mixed_i_words (weak_loose_words y) z v) (weak_loose_words y) HAP HRP HNP EH E2 E3 EK EU EI ES E0N EM EQ EN EA SepN
      BZ BoundH (double_tight_loose _ TightX) BoundI (double_tight_loose _ TightY) HC XP YP ZP H U1 I S1
      PFP HFP F2P F3P FKP UFP IFP SFP)
      as (mf & CN & XO & YO & ZO & FlagO & PFO & HFO & F2O & F3O & FKO & UFO & IFO & SFO & BXO & BYO & BZO & FN).
    assert (AFO : Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_finite_owned AFP FN).
    assert (VFO : Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_finite_owned VFP FN).
    assert (TFO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_finite_owned TFP FN).
    assert (ZFO : Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_finite_owned ZFP FN).
    assert (Frame : lframe (mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk) m mf).
    { eapply lframe_trans.
      - eapply lframe_implies;[exact FP|];intros bx pos ((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & N2 & N3 & NK) HV.
        unfold mixed_finite_difference_frame,mixed_prepare_frame;repeat split;try assumption;left;assumption.
      - eapply lframe_implies;[exact FN|];intros bx pos ((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & N2 & N3 & NK) HV.
        unfold mixed_nonzero_tail_frame;repeat split;try assumption;left;exact NP. }
    exists mf;split.
    + rewrite mixed_finite_difference_source;eapply exec_statement_prefix_then_last;[exact CP|exact CN].
    + repeat (first [assumption|split]).
Qed.

Require Import C.jet_secp_mixed_body C.jet_secp_mixed_head C.jet_secp_mixed_infinite_literal C.jet_secp_point_set_bit.

Definition mixed_loose_body_x_words flag x y z u v :=
  if Int.eq flag Int.zero then mixed_loose_finite_x_words x y z u v else u.
Definition mixed_loose_body_y_words flag x y z u v :=
  if Int.eq flag Int.zero then mixed_loose_finite_y_words x y z u v else v.
Definition mixed_loose_body_z_words flag x y z u v :=
  if Int.eq flag Int.zero then mixed_loose_finite_z_words x y z u v else point_set_bit_words true.
Definition mixed_loose_body_flag flag x y z u v :=
  if Int.eq flag Int.zero then mixed_loose_finite_flag x y z u v else Int.zero.
Definition mixed_loose_body_temps le flag x y z u v :=
  if Int.eq flag Int.zero then mixed_loose_finite_body_temps le x y z u v else PTree.set _t'4 (Vint flag) le.
Local Ltac separate_body_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_body_owned HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;congruence.

Definition mixed_mode_body_x_words loose flag x y z u v :=
  if Int.eq flag Int.zero then mixed_mode_finite_x_words loose x y z u v else u.
Definition mixed_mode_body_y_words loose flag x y z u v :=
  if Int.eq flag Int.zero then mixed_mode_finite_y_words loose x y z u v else v.
Definition mixed_mode_body_z_words loose flag x y z u v :=
  if Int.eq flag Int.zero then mixed_mode_finite_z_words loose x y z u v else point_set_bit_words true.
Definition mixed_mode_body_flag loose flag x y z u v :=
  if Int.eq flag Int.zero then mixed_mode_finite_flag loose x y z u v else Int.zero.
Definition mixed_mode_body_temps loose le flag x y z u v :=
  if Int.eq flag Int.zero then mixed_mode_finite_body_temps loose le x y z u v else PTree.set _t'4 (Vint flag) le.

Theorem exec_mixed_body_owned_mode (loose:bool) e le m bp ba bu bv bs bt bz bh bi b2 b3 bk x y z u v flag :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) -> e!_t=Some (bk,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_gej_set_ge=None ->
  NoDup [bp;ba;bu;bv;bs;bt;bz;bh;bi;b2;b3;bk] ->
  Mem.load Mint32 m bp 120=Some (Vint flag) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
  mixed_x_body_bound loose x ->
  square_input_bounds y ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bz 0 40 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> Mem.range_perm m bk 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (mixed_mode_body_temps loose le flag x y z u v) mf (mixed_body_out flag (mixed_x_words loose x) z u) /\
  fe_at mf bp 0 (words5 (mixed_mode_body_x_words loose flag x y z u v)) /\
  fe_at mf bp 40 (words5 (mixed_mode_body_y_words loose flag x y z u v)) /\
  fe_at mf bp 80 (words5 (mixed_mode_body_z_words loose flag x y z u v)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_mode_body_flag loose flag x y z u v)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\ Mem.range_perm mf bk 0 40 Cur Freeable /\
  square_input_bounds (mixed_mode_body_x_words loose flag x y z u v) /\ square_input_bounds (mixed_mode_body_y_words loose flag x y z u v) /\
  square_input_bounds (mixed_mode_body_z_words loose flag x y z u v) /\
  lframe (mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk) m mf.
Proof.
  intros HA HB HR HN EU EV ES ET EZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF EG Sep FlagA FlagB BX BY BZ BU BV
    X Y Z U V PF AF UF VF SF TF ZF HF IF F2 F3 FK.
  unfold mixed_mode_body_temps,mixed_body_out,mixed_mode_body_x_words,mixed_mode_body_y_words,mixed_mode_body_z_words,mixed_mode_body_flag.
  destruct (Int.eq_dec flag Int.zero) as [->|HFlag].
  - rewrite Int.eq_true.
    exact (exec_mixed_finite_body_mode loose e le m bp ba bu bv bs bt bz bh bi b2 b3 bk x y z u v
      HA HB HR HN EU EV ES ET EZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF Sep FlagA FlagB BX BY BZ BU BV
      X Y Z U V PF AF UF VF SF TF ZF HF IF F2 F3 FK).
  - rewrite Int.eq_false by exact HFlag;separate_body_blocks Sep.
    destruct (mixed_infinite_body_owned e le m bp ba u v flag HA HR HB HN EG ltac:(congruence) PF FlagA HFlag U V FlagB)
      as (mf & CB & XO & YO & ZO & FlagO & PFO & FB).
    assert (AFO : Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_body_owned AF FB).
    assert (UFO : Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_body_owned UF FB).
    assert (VFO : Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_body_owned VF FB).
    assert (SFO : Mem.range_perm mf bs 0 40 Cur Freeable) by (keep_body_owned SF FB).
    assert (TFO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_body_owned TF FB).
    assert (ZFO : Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_body_owned ZF FB).
    assert (HFO : Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_body_owned HF FB).
    assert (IFO : Mem.range_perm mf bi 0 40 Cur Freeable) by (keep_body_owned IF FB).
    assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_body_owned F2 FB).
    assert (F3O : Mem.range_perm mf b3 0 40 Cur Freeable) by (keep_body_owned F3 FB).
    assert (FKO : Mem.range_perm mf bk 0 40 Cur Freeable) by (keep_body_owned FK FB).
    assert (Frame : lframe (mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk) m mf).
    { eapply lframe_implies;[exact FB|];intros bx pos ((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & N2 & N3 & NK) HV;exact NP. }
    exists mf;repeat (first [assumption|exact mixed_one_bounds|split]).
Qed.

(** Existing positioned-X contracts remain exact specializations. *)
Theorem exec_mixed_finite_body_loose e le m bp ba bu bv bs bt bz bh bi b2 b3 bk x y z u v :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) -> e!_t=Some (bk,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None ->
  NoDup [bp;ba;bu;bv;bs;bt;bz;bh;bi;b2;b3;bk] ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  square_input_bounds y ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bz 0 40 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> Mem.range_perm m bk 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (mixed_loose_finite_body_temps le x y z u v) mf (mixed_finite_body_out x z u) /\
  fe_at mf bp 0 (words5 (mixed_loose_finite_x_words x y z u v)) /\
  fe_at mf bp 40 (words5 (mixed_loose_finite_y_words x y z u v)) /\
  fe_at mf bp 80 (words5 (mixed_loose_finite_z_words x y z u v)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_loose_finite_flag x y z u v)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\ Mem.range_perm mf bk 0 40 Cur Freeable /\
  square_input_bounds (mixed_loose_finite_x_words x y z u v) /\ square_input_bounds (mixed_loose_finite_y_words x y z u v) /\
  square_input_bounds (mixed_loose_finite_z_words x y z u v) /\
  lframe (mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk) m mf.
Proof.
  exact (exec_mixed_finite_body_mode false e le m bp ba bu bv bs bt bz bh bi b2 b3 bk x y z u v).
Qed.

Theorem exec_mixed_body_owned_loose e le m bp ba bu bv bs bt bz bh bi b2 b3 bk x y z u v flag :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) -> e!_t=Some (bk,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_gej_set_ge=None ->
  NoDup [bp;ba;bu;bv;bs;bt;bz;bh;bi;b2;b3;bk] ->
  Mem.load Mint32 m bp 120=Some (Vint flag) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  square_input_bounds y ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bz 0 40 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> Mem.range_perm m bk 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (mixed_loose_body_temps le flag x y z u v) mf (mixed_body_out flag x z u) /\
  fe_at mf bp 0 (words5 (mixed_loose_body_x_words flag x y z u v)) /\
  fe_at mf bp 40 (words5 (mixed_loose_body_y_words flag x y z u v)) /\
  fe_at mf bp 80 (words5 (mixed_loose_body_z_words flag x y z u v)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_loose_body_flag flag x y z u v)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\ Mem.range_perm mf bk 0 40 Cur Freeable /\
  square_input_bounds (mixed_loose_body_x_words flag x y z u v) /\ square_input_bounds (mixed_loose_body_y_words flag x y z u v) /\
  square_input_bounds (mixed_loose_body_z_words flag x y z u v) /\
  lframe (mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk) m mf.
Proof.
  exact (exec_mixed_body_owned_mode false e le m bp ba bu bv bs bt bz bh bi b2 b3 bk x y z u v flag).
Qed.
