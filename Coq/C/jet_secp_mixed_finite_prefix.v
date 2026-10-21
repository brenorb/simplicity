(** The original finite mixed-addition prefix through H and I. All intermediate
    storage, permissions and operand bounds are derived from the initial state. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_curve_frame
  C.jet_secp_field_read_preservation C.jet_secp_statement_prefix C.jet_secp_mixed_preparation
  C.jet_secp_mixed_difference C.jet_secp_double_coordinate_numeric C.jet_secp_square_execution
  C.jet_secp_curve_statements C.jet_secp_square_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words mixed_difference_words.

Lemma mixed_positioned_tight w :
  fe_limbs_ok (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
    (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) ->
  mul_small_input_bounds w.
Proof.
  intros HB i HI;unfold fe_limbs_ok in HB.
  destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb];lia.
Qed.

Definition mixed_finite_difference_statements :=
  mixed_finite_preparation_statements++mixed_difference_statements.
Definition mixed_finite_difference_frame bp ba bu bv bs bt bz bh bi bx pos :=
  mixed_prepare_frame bp ba bu bv bs bt bz bx pos /\ bx<>bh /\ bx<>bi.
Lemma mixed_finite_difference_source : fn_body f_secp256k1_gej_add_ge_var=
  statement_sequence mixed_finite_difference_statements mixed_after_difference.
Proof. reflexivity. Qed.

Local Ltac separate_prefix_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_prefix_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac keep_prefix_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.

Theorem exec_mixed_finite_difference e le m bp ba bu bv bs bt bz bh bi x y z u v :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
  NoDup [bh;bi;bp;ba;bu;bv;bs;bt;bz] ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
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
  exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_finite_difference_statements Sskip) E0
    (mixed_preparation_temps le) mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 z) /\
  fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\
  fe_at mf bu 0 (words5 x) /\ fe_at mf bv 0 (words5 (point_mul_words u (square_words z))) /\
  fe_at mf bs 0 (words5 y) /\ fe_at mf bt 0 (words5 (point_mul_words (point_mul_words v (square_words z)) z)) /\
  fe_at mf bz 0 (words5 (square_words z)) /\
  fe_at mf bh 0 (words5 (mixed_difference_words x (point_mul_words u (square_words z)))) /\
  fe_at mf bi 0 (words5 (mixed_difference_words (point_mul_words (point_mul_words v (square_words z)) z) y)) /\
  Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\ Mem.load Mint32 mf ba 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  mul_small_input_bounds x /\ mul_small_input_bounds y /\
  mul_small_input_bounds (point_mul_words u (square_words z)) /\
  mul_small_input_bounds (point_mul_words (point_mul_words v (square_words z)) z) /\
  radix_value (mixed_difference_words x (point_mul_words u (square_words z)))=
    4*feP-radix_value x+radix_value (point_mul_words u (square_words z)) /\
  radix_value (mixed_difference_words (point_mul_words (point_mul_words v (square_words z)) z) y)=
    4*feP-radix_value (point_mul_words (point_mul_words v (square_words z)) z)+radix_value y /\
  square_input_bounds (mixed_difference_words x (point_mul_words u (square_words z))) /\
  square_input_bounds (mixed_difference_words (point_mul_words (point_mul_words v (square_words z)) z) y) /\
  lframe (mixed_finite_difference_frame bp ba bu bv bs bt bz bh bi) m mf.
Proof.
  intros HA HB EU EV ES ET EZ EH EI EW EM EQ EN EA Sep FlagA FlagB BX BY BZ BU BV
    X Y Z U V PF AF UF VF SF TF ZF HF IF.
  assert (SepP : NoDup [bp;ba;bu;bv;bs;bt;bz]).
  { apply NoDup_cons_iff in Sep as [_ Sep];apply NoDup_cons_iff in Sep as [_ Sep];exact Sep. }
  separate_prefix_blocks Sep.
  assert (SepD : NoDup [bh;bi;bu;bv;bs;bt]) by (repeat constructor;cbn [In];tauto).
  destruct (exec_mixed_finite_preparation e le m bp ba bu bv bs bt bz x y z u v
    HA HB EU EV ES ET EZ EW EM EQ SepP FlagA FlagB BX BY BZ BU BV X Y Z U V PF AF UF VF SF TF ZF)
    as (mp & CP & XP & YP & ZP & UP & VP & U1 & U2 & S1 & S2 & Z12 & FlagAP & FlagBP &
      PFP & AFP & UFP & VFP & SFP & TFP & ZFP & BoundZ & BoundU & BoundS & FP).
  assert (HFP : Mem.range_perm mp bh 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact HF|exact FP|];intro pos;unfold mixed_prepare_frame;
      repeat split;try (left;congruence);congruence. }
  assert (IFP : Mem.range_perm mp bi 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact IF|exact FP|];intro pos;unfold mixed_prepare_frame;
      repeat split;try (left;congruence);congruence. }
  pose proof (mixed_positioned_tight x BX) as TightX.
  pose proof (mixed_positioned_tight y BY) as TightY.
  pose proof (double_mul_tight u (square_words z) BU BoundZ) as TightU.
  pose proof (double_mul_tight v (square_words z) BV BoundZ) as TightS0.
  pose proof (double_mul_tight (point_mul_words v (square_words z)) z
    (double_tight_loose _ TightS0) BZ) as TightS.
  destruct (exec_mixed_differences e (mixed_preparation_temps le) mp bh bi bu bv bs bt
    x (point_mul_words u (square_words z)) y (point_mul_words (point_mul_words v (square_words z)) z)
    EH EI EU EV ES ET EN EA SepD TightX TightU TightY TightS U1 U2 S1 S2 HFP IFP UFP VFP SFP TFP)
    as (mf & CD & HO & IO & U1O & U2O & S1O & S2O & HFO & IFO & UFO & VFO & SFO & TFO &
      ValH & ValI & BoundH & BoundI & FD).
  assert (XO : fe_at mf bp 0 (words5 x)) by (keep_prefix_field XP FD).
  assert (YO : fe_at mf bp 40 (words5 y)) by (keep_prefix_field YP FD).
  assert (ZO : fe_at mf bp 80 (words5 z)) by (keep_prefix_field ZP FD).
  assert (UO : fe_at mf ba 0 (words5 u)) by (keep_prefix_field UP FD).
  assert (VO : fe_at mf ba 40 (words5 v)) by (keep_prefix_field VP FD).
  assert (Z12O : fe_at mf bz 0 (words5 (square_words z))) by (keep_prefix_field Z12 FD).
  assert (PFO : Mem.range_perm mf bp 0 128 Cur Freeable) by (keep_prefix_free PFP FD).
  assert (AFO : Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_prefix_free AFP FD).
  assert (ZFO : Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_prefix_free ZFP FD).
  assert (FlagAO : Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FD Mint32 bp 120);[exact FlagAP| |intros pos HP;repeat split;congruence].
    eapply Mem.perm_valid_block;apply (PFP 0);lia. }
  assert (FlagBO : Mem.load Mint32 mf ba 80=Some (Vint Int.zero)).
  { rewrite (proj1 FD Mint32 ba 80);[exact FlagBP| |intros pos HP;repeat split;congruence].
    eapply Mem.perm_valid_block;apply (AFP 0);lia. }
  assert (Frame : lframe (mixed_finite_difference_frame bp ba bu bv bs bt bz bh bi) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FP|];intros bx pos (HP & NH & NI) HV;exact HP.
    - eapply lframe_implies;[exact FD|];intros bx pos ((NU & NV & NS & NT & NZ & NP & NA) & NH & NI) HV;
        repeat split;assumption. }
  exists mf;split.
  - change (Clight2.exec_stmt secp_ge e le m
      (statement_sequence mixed_finite_preparation_statements (statement_sequence mixed_difference_statements Sskip))
      E0 (mixed_preparation_temps le) mf Out_normal).
    eapply exec_statement_prefix_then_last;[exact CP|exact CD].
  - repeat (first [assumption|split]).
Qed.
