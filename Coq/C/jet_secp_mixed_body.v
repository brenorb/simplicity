(** Complete original in-place mixed-addition body with NULL rzr. Both the
    incoming-infinity branch and every finite H/I branch are covered. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_mixed_finite_return C.jet_secp_mixed_finite_body C.jet_secp_mixed_head
  C.jet_secp_mixed_infinite_literal C.jet_secp_point_set_bit.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_body_x_words flag x y z u v :=
  if Int.eq flag Int.zero then mixed_finite_x_words x y z u v else u.
Definition mixed_body_y_words flag x y z u v :=
  if Int.eq flag Int.zero then mixed_finite_y_words x y z u v else v.
Definition mixed_body_z_words flag x y z u v :=
  if Int.eq flag Int.zero then mixed_finite_z_words x y z u v else point_set_bit_words true.
Definition mixed_body_flag flag x y z u v :=
  if Int.eq flag Int.zero then mixed_finite_flag x y z u v else Int.zero.
Definition mixed_body_temps le flag x y z u v :=
  if Int.eq flag Int.zero then mixed_finite_body_temps le x y z u v else PTree.set _t'4 (Vint flag) le.
Definition mixed_body_out flag x z u :=
  if Int.eq flag Int.zero then mixed_finite_body_out x z u else Out_return None.

Local Ltac separate_body_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_body_owned HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;congruence.

Theorem exec_mixed_body_owned e le m bp ba bu bv bs bt bz bh bi b2 b3 bk x y z u v flag :
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
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bz 0 40 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> Mem.range_perm m bk 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (mixed_body_temps le flag x y z u v) mf (mixed_body_out flag x z u) /\
  fe_at mf bp 0 (words5 (mixed_body_x_words flag x y z u v)) /\
  fe_at mf bp 40 (words5 (mixed_body_y_words flag x y z u v)) /\
  fe_at mf bp 80 (words5 (mixed_body_z_words flag x y z u v)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_body_flag flag x y z u v)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\ Mem.range_perm mf bk 0 40 Cur Freeable /\
  square_input_bounds (mixed_body_x_words flag x y z u v) /\ square_input_bounds (mixed_body_y_words flag x y z u v) /\
  square_input_bounds (mixed_body_z_words flag x y z u v) /\
  lframe (mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk) m mf.
Proof.
  intros HA HB HR HN EU EV ES ET EZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF EG Sep FlagA FlagB BX BY BZ BU BV
    X Y Z U V PF AF UF VF SF TF ZF HF IF F2 F3 FK.
  unfold mixed_body_temps,mixed_body_out,mixed_body_x_words,mixed_body_y_words,mixed_body_z_words,mixed_body_flag.
  destruct (Int.eq_dec flag Int.zero) as [->|HFlag].
  - rewrite Int.eq_true.
    exact (exec_mixed_finite_body e le m bp ba bu bv bs bt bz bh bi b2 b3 bk x y z u v
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
