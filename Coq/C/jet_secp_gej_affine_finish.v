(** Execute the unchanged affine-conversion suffix, starting with its
    already-inverted Z. No inversion correctness is asserted here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv.
Require Import C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_point_write_run.
Require Import C.jet_secp_gej_affine_arithmetic C.jet_secp_ge_set_xy C.jet_secp_point_set_bit.
Require Import C.jet_secp_statement_prefix C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage.
Require Import C.jet_secp_multiply_finish_product C.jet_secp_multiply_checkpoint_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words.

Definition affine_set_one_statement := curve_call _secp256k1_fe_set_int f_secp256k1_fe_set_int None
  [affine_point_address _z;Econst_int Int.one tint].
Definition affine_set_xy_statement := curve_call _secp256k1_ge_set_xy f_secp256k1_ge_set_xy None
  [Etempvar _r (tptr curve_ge_type);affine_point_address _x;affine_point_address _y].
Lemma affine_finish_source : affine_finish_statement = Ssequence affine_set_one_statement affine_set_xy_statement.
Proof. reflexivity. Qed.
Definition affine_finish_frame (bp bd bx : block) pos :=
  bx<>bd /\ (bx<>bp \/ pos<80 \/ 120<=pos).

Theorem exec_affine_finish le m bp bd b2 b3 x y :
  le!_a=Some(Vptr bp Ptrofs.zero) -> le!_r=Some(Vptr bd Ptrofs.zero) -> bp<>bd ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge (affine_local_env b2 b3) le m affine_finish_statement E0 le mf Out_normal /\
  fe_at mf bd 0 (words5 x) /\ fe_at mf bd 40 (words5 y) /\
  Mem.load Mint32 mf bd 80=Some(Vint Int.zero) /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\
  fe_at mf bp 80 (words5 (point_set_bit_words true)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
  lframe (affine_finish_frame bp bd) m mf.
Proof.
  intros HA HR Sep X Y FP FD.
  destruct (eval_point_set_bit PointZ true m bp FP) as (m1 & C1 & Z1 & FP1 & L1).
  assert (X1 : fe_at m1 bp 0 (words5 x)).
  { eapply curve_keep_field_range;[reflexivity|exact X|exact L1|];intros pos HP;right;left;cbn;lia. }
  assert (Y1 : fe_at m1 bp 40 (words5 y)).
  { eapply curve_keep_field_range;[reflexivity|exact Y|exact L1|];intros pos HP;right;left;cbn;lia. }
  assert (FD1 : Mem.range_perm m1 bd 0 88 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FD|exact L1|];intro pos;left;congruence. }
  destruct (eval_ge_set_xy_owned x y m1 bd bp ltac:(congruence) X1 Y1 FD1)
    as (mf & C2 & XO & YO & Flag & FDF & Perm & L2).
  assert (XF : fe_at mf bp 0 (words5 x)).
  { eapply curve_keep_field_range;[reflexivity|exact X1|exact L2|];intros;exact Sep. }
  assert (YF : fe_at mf bp 40 (words5 y)).
  { eapply curve_keep_field_range;[reflexivity|exact Y1|exact L2|];intros;exact Sep. }
  assert (ZF : fe_at mf bp 80 (words5 (point_set_bit_words true))).
  { eapply curve_keep_field_range;[reflexivity|exact Z1|exact L2|];intros;exact Sep. }
  assert (FPF : Mem.range_perm mf bp 0 128 Cur Freeable).
  { intros pos HP;apply (proj2 (Perm bp pos Cur Freeable));apply FP1;exact HP. }
  assert (Frame : lframe (affine_finish_frame bp bd) m mf).
  { eapply lframe_trans; eapply lframe_implies;[exact L1| |exact L2|];
      intros bx pos [OutD OutP] Valid;assumption. }
  assert (Body : Clight2.exec_stmt secp_ge (affine_local_env b2 b3) le m affine_finish_statement E0 le mf Out_normal).
  { rewrite affine_finish_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
    - eapply exec_curve_call with (vargs:=[Vptr bp (Ptrofs.repr 80);Vint Int.one]) (v:=Vundef).
      + unfold secp_pure;repeat (first [left;reflexivity|right]).
      + reflexivity.
      + eapply eval_Econs;[apply eval_affine_point_address;[cbn [In];tauto|exact HA]|reflexivity|].
        eapply eval_Econs;[apply eval_Econst_int|reflexivity|apply eval_Enil].
      + exact C1.
    - eapply exec_curve_call with (vargs:=[Vptr bd Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr bp (Ptrofs.repr 40)]) (v:=Vundef).
      + unfold secp_pure;repeat (first [left;reflexivity|right]).
      + reflexivity.
      + eapply eval_Econs;[apply eval_Etempvar;exact HR|reflexivity|].
        eapply eval_Econs;[apply eval_affine_point_address;[cbn [In];tauto|exact HA]|reflexivity|].
        eapply eval_Econs;[apply eval_affine_point_address;[cbn [In];tauto|exact HA]|reflexivity|apply eval_Enil].
      + exact C2. }
  exists mf;repeat first [assumption|split].
Qed.

Lemma affine_local_blocks b2 b3 : blocks_of_env secp_ge (affine_local_env b2 b3) =
  [(b2,0,40);(b3,0,40)].
Proof. reflexivity. Qed.

Theorem affine_free_owned_locals m bd bp b2 b3 x y :
  b2<>b3 -> bd<>b2 -> bd<>b3 -> bp<>b2 -> bp<>b3 ->
  fe_at m bd 0 (words5 x) -> fe_at m bd 40 (words5 y) ->
  Mem.load Mint32 m bd 80=Some(Vint Int.zero) ->
  Mem.range_perm m bd 0 88 Cur Freeable -> Mem.range_perm m bp 0 128 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> exists mr,
  Mem.free_list m (blocks_of_env secp_ge (affine_local_env b2 b3))=Some mr /\
  fe_at mr bd 0 (words5 x) /\ fe_at mr bd 40 (words5 y) /\
  Mem.load Mint32 mr bd 80=Some(Vint Int.zero) /\
  Mem.range_perm mr bd 0 88 Cur Freeable /\ Mem.range_perm mr bp 0 128 Cur Freeable /\
  lframe (fun b _=>b<>b2 /\ b<>b3) m mr.
Proof.
  intros N23 D2 D3 P2 P3 X Y Flag FD FP F2 F3.
  destruct (free_list_exists [(b2,0,40);(b3,0,40)] m) as (mr & Free & Unchanged).
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [Eq|[Eq|Nil]];[inversion Eq;subst;exact F2|inversion Eq;subst;exact F3|contradiction].
  - assert (Frame : lframe (fun b _=>b<>b2 /\ b<>b3) m mr).
    { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
      intros b pos [Not2 Not3] Valid;cbn;intuition congruence. }
    assert (XR : fe_at mr bd 0 (words5 x)).
    { eapply curve_keep_field_range;[reflexivity|exact X|exact Frame|];intros;split;assumption. }
    assert (YR : fe_at mr bd 40 (words5 y)).
    { eapply curve_keep_field_range;[reflexivity|exact Y|exact Frame|];intros;split;assumption. }
    assert (Valid : Mem.valid_block m bd) by (eapply Mem.perm_valid_block;apply (FD 0);lia).
    assert (FlagR : Mem.load Mint32 mr bd 80=Some(Vint Int.zero)).
    { rewrite (proj1 Frame Mint32 bd 80 Valid);[exact Flag|intros;split;assumption]. }
    assert (FDR : Mem.range_perm mr bd 0 88 Cur Freeable).
    { eapply curve_keep_free;[lia|exact FD|exact Frame|];intros;split;assumption. }
    assert (FPR : Mem.range_perm mr bp 0 128 Cur Freeable).
    { eapply curve_keep_free;[lia|exact FP|exact Frame|];intros;split;assumption. }
    exists mr;rewrite affine_local_blocks;repeat first [assumption|split].
Qed.

Definition affine_after_inverse_frame bp bd b2 b3 bx pos :=
  affine_arithmetic_frame bp b2 b3 bx pos /\ bx<>bd.

Theorem exec_affine_after_inverse le m bp bd b2 b3 x y zi :
  le!_a=Some(Vptr bp Ptrofs.zero) -> le!_r=Some(Vptr bd Ptrofs.zero) ->
  bp<>b2 -> bp<>b3 -> b2<>b3 -> bd<>bp -> bd<>b2 -> bd<>b3 ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds zi ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 zi) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge (affine_local_env b2 b3) le m
    (affine_arithmetic_context affine_finish_statement) E0 le mf Out_normal /\
  fe_at mf bd 0 (words5 (point_mul_words x (square_words zi))) /\
  fe_at mf bd 40 (words5 (point_mul_words y (point_mul_words zi (square_words zi)))) /\
  Mem.load Mint32 mf bd 80=Some(Vint Int.zero) /\
  fe_at mf bp 0 (words5 (point_mul_words x (square_words zi))) /\
  fe_at mf bp 40 (words5 (point_mul_words y (point_mul_words zi (square_words zi)))) /\
  fe_at mf bp 80 (words5 (point_set_bit_words true)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
  square_input_bounds (point_mul_words x (square_words zi)) /\
  square_input_bounds (point_mul_words y (point_mul_words zi (square_words zi))) /\
  radix_value (point_mul_words x (square_words zi)) mod field_prime =
    (radix_value x * (radix_value zi * radix_value zi)) mod field_prime /\
  radix_value (point_mul_words y (point_mul_words zi (square_words zi))) mod field_prime =
    (radix_value y * (radix_value zi * (radix_value zi * radix_value zi))) mod field_prime /\
  lframe (affine_after_inverse_frame bp bd b2 b3) m mf.
Proof.
  intros HA HR P2 P3 N23 DP D2 D3 BX BY BZ X Y Z FP FD F2 F3.
  destruct (exec_affine_arithmetic le m bp b2 b3 x y zi HA P2 P3 N23 BX BY BZ X Y Z FP F2 F3)
    as (ma & Arithmetic & XA & YA & ZA & S & T & FPA & F2A & F3A & BXO & BYO & VX & VY & LA).
  assert (FDA : Mem.range_perm ma bd 0 88 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FD|exact LA|].
    intro pos;unfold affine_arithmetic_frame;intros [[Eq _]|[[Eq _]|[Eq _]]];congruence. }
  destruct (exec_affine_finish le ma bp bd b2 b3
    (point_mul_words x (square_words zi)) (point_mul_words y (point_mul_words zi (square_words zi)))
    HA HR ltac:(congruence) XA YA FPA FDA)
    as (mf & Finish & XO & YO & Flag & XF & YF & ZF & FPF & FDF & LF).
  assert (F2F : Mem.range_perm mf b2 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F2A|exact LF|].
    intro pos;split;[congruence|left;congruence]. }
  assert (F3F : Mem.range_perm mf b3 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F3A|exact LF|].
    intro pos;split;[congruence|left;congruence]. }
  assert (Frame : lframe (affine_after_inverse_frame bp bd b2 b3) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact LA|];intros bx pos [Outside NotD] Valid;exact Outside.
    - eapply lframe_implies;[exact LF|];intros bx pos [Outside NotD] Valid.
      split;[exact NotD|].
      destruct (Pos.eq_dec bx bp) as [Eq|NE];[subst bx|left;exact NE].
      unfold affine_arithmetic_frame in Outside;destruct (Z_lt_ge_dec pos 80);
        [right;left;lia|right;right;intuition lia]. }
  exists mf;split.
  - change (Clight2.exec_stmt secp_ge (affine_local_env b2 b3) le m
      (statement_sequence [affine_square_statement;affine_cube_statement;
        affine_coordinate_statement false;affine_coordinate_statement true] affine_finish_statement)
      E0 le mf Out_normal).
    eapply exec_statement_prefix_then_last;[exact Arithmetic|exact Finish].
  - repeat first [assumption|split].
Qed.

Theorem exec_affine_after_inverse_and_free le m bp bd b2 b3 x y zi :
  le!_a=Some(Vptr bp Ptrofs.zero) -> le!_r=Some(Vptr bd Ptrofs.zero) ->
  bp<>b2 -> bp<>b3 -> b2<>b3 -> bd<>bp -> bd<>b2 -> bd<>b3 ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds zi ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 zi) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> exists mf mr,
  Clight2.exec_stmt secp_ge (affine_local_env b2 b3) le m
    (affine_arithmetic_context affine_finish_statement) E0 le mf Out_normal /\
  Mem.free_list mf (blocks_of_env secp_ge (affine_local_env b2 b3))=Some mr /\
  fe_at mr bd 0 (words5 (point_mul_words x (square_words zi))) /\
  fe_at mr bd 40 (words5 (point_mul_words y (point_mul_words zi (square_words zi)))) /\
  Mem.load Mint32 mr bd 80=Some(Vint Int.zero) /\
  Mem.range_perm mr bp 0 128 Cur Freeable /\ Mem.range_perm mr bd 0 88 Cur Freeable /\
  square_input_bounds (point_mul_words x (square_words zi)) /\
  square_input_bounds (point_mul_words y (point_mul_words zi (square_words zi))) /\
  radix_value (point_mul_words x (square_words zi)) mod field_prime =
    (radix_value x * (radix_value zi * radix_value zi)) mod field_prime /\
  radix_value (point_mul_words y (point_mul_words zi (square_words zi))) mod field_prime =
    (radix_value y * (radix_value zi * (radix_value zi * radix_value zi))) mod field_prime /\
  lframe (fun bx pos=>affine_after_inverse_frame bp bd b2 b3 bx pos /\ bx<>b2 /\ bx<>b3) m mr.
Proof.
  intros HA HR P2 P3 N23 DP D2 D3 BX BY BZ X Y Z FP FD F2 F3.
  destruct (exec_affine_after_inverse le m bp bd b2 b3 x y zi
    HA HR P2 P3 N23 DP D2 D3 BX BY BZ X Y Z FP FD F2 F3)
    as (mf & Body & XO & YO & Flag & XF & YF & ZF & FPF & FDF & F2F & F3F & BXO & BYO & VX & VY & LF).
  destruct (affine_free_owned_locals mf bd bp b2 b3
    (point_mul_words x (square_words zi)) (point_mul_words y (point_mul_words zi (square_words zi)))
    N23 D2 D3 P2 P3 XO YO Flag FDF FPF F2F F3F)
    as (mr & Free & XR & YR & FlagR & FDR & FPR & LR).
  assert (Frame : lframe (fun bx pos=>affine_after_inverse_frame bp bd b2 b3 bx pos /\ bx<>b2 /\ bx<>b3) m mr).
  { eapply lframe_trans; eapply lframe_implies;[exact LF| |exact LR|];
      intros bx pos [Outside NotLocal] Valid;assumption. }
  exists mf,mr;repeat first [assumption|split].
Qed.
