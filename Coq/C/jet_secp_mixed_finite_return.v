(** Entire original mixed-addition body on the finite H=0 path, from initial
    point/affine storage and uninitialized private fields through its return. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_statement_prefix C.jet_secp_mixed_preparation C.jet_secp_mixed_finite_prefix
  C.jet_secp_mixed_difference C.jet_secp_mixed_zero_return C.jet_secp_double_coordinate_numeric
  C.jet_secp_double_all_calls C.jet_secp_field_read_preservation.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words mixed_difference_words.

Definition mixed_h_words x z u := mixed_difference_words x (point_mul_words u (square_words z)).
Definition mixed_i_words y z v := mixed_difference_words (point_mul_words (point_mul_words v (square_words z)) z) y.
Definition mixed_finite_return_frame (bp ba bu bv bs bt bz bh bi bx : block) (_ : Z) :=
  bx<>bp /\ bx<>ba /\ bx<>bu /\ bx<>bv /\ bx<>bs /\ bx<>bt /\ bx<>bz /\ bx<>bh /\ bx<>bi.

Local Ltac separate_return_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_return_owned HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.

Theorem exec_mixed_finite_zero_body e le m bp ba bu bv bs bt bz bh bi x y z u v :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None ->
  NoDup [bh;bi;bp;ba;bu;bv;bs;bt;bz] ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v -> radix_value (mixed_h_words x z u) mod feP=0 ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bz 0 40 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (mixed_zero_return_temps (mixed_preparation_temps le) (mixed_i_words y z v)) mf (Out_return None) /\
  fe_at mf bp 0 (words5 (mixed_zero_words (mixed_i_words y z v) (double_output_x_words x y))) /\
  fe_at mf bp 40 (words5 (mixed_zero_words (mixed_i_words y z v) (double_output_y_words x y))) /\
  fe_at mf bp 80 (words5 (mixed_zero_words (mixed_i_words y z v) (double_output_z_words y z))) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_zero_flag (mixed_i_words y z v) y z)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  square_input_bounds (mixed_zero_words (mixed_i_words y z v) (double_output_x_words x y)) /\
  square_input_bounds (mixed_zero_words (mixed_i_words y z v) (double_output_y_words x y)) /\
  square_input_bounds (mixed_zero_words (mixed_i_words y z v) (double_output_z_words y z)) /\
  lframe (mixed_finite_return_frame bp ba bu bv bs bt bz bh bi) m mf.
Proof.
  intros HA HB HR HN EU EV ES ET EZ EH EI EW EM EQ EN EA E0N ED EF Sep FlagA FlagB BX BY BZ BU BV HZ
    X Y Z U V PF AF UF VF SF TF ZF HF IF.
  pose proof Sep as Sep0;separate_return_blocks Sep.
  destruct (exec_mixed_finite_difference e le m bp ba bu bv bs bt bz bh bi x y z u v
    HA HB EU EV ES ET EZ EH EI EW EM EQ EN EA Sep0 FlagA FlagB BX BY BZ BU BV X Y Z U V PF AF UF VF SF TF ZF HF IF)
    as (mp & CP & XP & YP & ZP & UP & VP & U1 & U2 & S1 & S2 & Z12 & H & I & FlagAP & FlagBP &
      PFP & AFP & UFP & VFP & SFP & TFP & ZFP & HFP & IFP & TightX & TightY & TightU & TightS &
      ValH & ValI & BoundH & BoundI & FP).
  assert (HAP : (mixed_preparation_temps le)!_a=Some (Vptr bp Ptrofs.zero)).
  { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HA. }
  assert (HRP : (mixed_preparation_temps le)!_r=Some (Vptr bp Ptrofs.zero)).
  { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HR. }
  assert (HNP : (mixed_preparation_temps le)!_rzr=Some (Vlong Int64.zero)).
  { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HN. }
  destruct (exec_mixed_zero_return e (mixed_preparation_temps le) mp bp bh bi x y z
    (mixed_h_words x z u) (mixed_i_words y z v) HAP HRP HNP EH EI E0N ED EF
    ltac:(congruence) ltac:(congruence) ltac:(congruence)
    (double_tight_loose _ TightX) (double_tight_loose _ TightY) BZ BoundH BoundI HZ FlagAP XP YP ZP H I PFP HFP IFP)
    as (mf & CR & XO & YO & ZO & FlagO & HO & IO & PFO & HFO & IFO & BXO & BYO & BZO & FR).
  assert (AFO : Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_return_owned AFP FR).
  assert (UFO : Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_return_owned UFP FR).
  assert (VFO : Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_return_owned VFP FR).
  assert (SFO : Mem.range_perm mf bs 0 40 Cur Freeable) by (keep_return_owned SFP FR).
  assert (TFO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_return_owned TFP FR).
  assert (ZFO : Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_return_owned ZFP FR).
  assert (Frame : lframe (mixed_finite_return_frame bp ba bu bv bs bt bz bh bi) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FP|].
      intros bx pos (NP & NA & NU & NV & NS & NT & NZ & NH & NI) HV.
      unfold mixed_finite_difference_frame,mixed_prepare_frame;repeat split;try assumption;left;assumption.
    - eapply lframe_implies;[exact FR|].
      intros bx pos (NP & NA & NU & NV & NS & NT & NZ & NH & NI) HV;repeat split;assumption. }
  exists mf;split.
  - rewrite mixed_finite_difference_source;eapply exec_statement_prefix_then_last;[exact CP|exact CR].
  - repeat (first [assumption|split]).
Qed.
