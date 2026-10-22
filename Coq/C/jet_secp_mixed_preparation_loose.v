(** Original mixed-addition preparation on a loose Y coordinate.
    Retain the actual normalized S1 rather than assuming that Y is unchanged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_curve_square C.jet_secp_point_write_run
  C.jet_secp_curve_statements C.jet_secp_mixed_finite_start C.jet_secp_mixed_copy_weak
  C.jet_secp_mixed_affine_product C.jet_secp_mixed_s2_calls C.jet_secp_field_weak_tight
  C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_statement_prefix
  C.jet_secp_mixed_head C.jet_secp_double_statements C.jet_secp_point_square_coordinate C.jet_secp_square_numeric.
Require Import C.jet_secp_field_weak_loose C.jet_secp_mixed_copy_weak_loose C.jet_secp_mixed_preparation.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words weak_loose_words.

Local Ltac separate_blocks HSep :=
  repeat rewrite NoDup_cons_iff in HSep;cbn [In] in HSep;
  repeat match goal with HN : _ /\ _ |- _ => destruct HN end;
  repeat match goal with HN : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by tauto;assert (HQ : ~Q) by tauto;clear HN
  end.
Local Ltac geometry arithmetic :=
  cbv beta delta [curve_square_offset mixed_s2_frame mixed_prepare_frame];
  lazymatch goal with
  | |- _ /\ _ => split;geometry arithmetic
  | |- ?a <> ?b \/ _ =>
      tryif constr_eq a b then (right;first [left;arithmetic | right;arithmetic])
      else (left;congruence)
  | |- _ <> _ => congruence
  end.
Local Ltac keep_field HF Frame :=
  eapply curve_keep_field_range;[reflexivity|exact HF|exact Frame|intros pos HP;geometry ltac:(clear - HP;lia)].
Local Ltac keep_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|intro pos;geometry ltac:(fail "same-block ownership needs a range proof")].

Theorem exec_mixed_preparation_loose e le m bp ba bu bv bs bt bz x y z u v t :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None ->
  NoDup [bp;ba;bu;bv;bs;bt;bz] ->
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  (forall i,(i<5)%nat -> Int64.unsigned (y i)<=2^60) ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v -> square_input_bounds t ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bz 0 (words5 t) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_preparation_statements Sskip) E0 le mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 z) /\
  fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\
  fe_at mf bu 0 (words5 x) /\ fe_at mf bv 0 (words5 (point_mul_words u t)) /\
  fe_at mf bs 0 (words5 (weak_loose_words y)) /\ fe_at mf bt 0 (words5 (point_mul_words (point_mul_words v t) z)) /\
  fe_at mf bz 0 (words5 t) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
  square_input_bounds (point_mul_words u t) /\ square_input_bounds (point_mul_words (point_mul_words v t) z) /\
  lframe (mixed_prepare_frame bp ba bu bv bs bt bz) m mf.
Proof.
  intros HA HB EU EV ES ET EZ EW EM Sep BX BY BZ BU BV BT X Y Z U V T PF AF UF VF SF TF ZF.
  separate_blocks Sep.
  destruct (exec_mixed_copy_weak e le m bp bu false x HA EU EW ltac:(congruence) BX X PF UF)
    as (mc1 & m1 & C1 & C2 & U1 & UF1 & X1 & PF1 & F1).
  assert (Y1 : fe_at m1 bp 40 (words5 y)) by (keep_field Y F1).
  assert (Z1 : fe_at m1 bp 80 (words5 z)) by (keep_field Z F1).
  assert (A1 : fe_at m1 ba 0 (words5 u)) by (keep_field U F1).
  assert (B1 : fe_at m1 ba 40 (words5 v)) by (keep_field V F1).
  assert (T1 : fe_at m1 bz 0 (words5 t)) by (keep_field T F1).
  assert (AF1 : Mem.range_perm m1 ba 0 88 Cur Freeable) by (keep_free AF F1).
  assert (VF1 : Mem.range_perm m1 bv 0 40 Cur Freeable) by (keep_free VF F1).
  assert (SF1 : Mem.range_perm m1 bs 0 40 Cur Freeable) by (keep_free SF F1).
  assert (TF1 : Mem.range_perm m1 bt 0 40 Cur Freeable) by (keep_free TF F1).
  assert (ZF1 : Mem.range_perm m1 bz 0 40 Cur Freeable) by (keep_free ZF F1).
  destruct (exec_mixed_affine_call false u t e le m1 bv ba bz EV EZ HB EM BU BT
    ltac:(congruence) ltac:(congruence) ltac:(congruence) VF1 A1 AF1 T1 ZF1)
    as (m2 & C3 & V2 & A2 & T2 & VF2 & AF2 & ZF2 & ValU & BoundU & F2).
  assert (X2 : fe_at m2 bp 0 (words5 x)) by (keep_field X1 F2).
  assert (Y2 : fe_at m2 bp 40 (words5 y)) by (keep_field Y1 F2).
  assert (Z2 : fe_at m2 bp 80 (words5 z)) by (keep_field Z1 F2).
  assert (B2 : fe_at m2 ba 40 (words5 v)) by (keep_field B1 F2).
  assert (U2 : fe_at m2 bu 0 (words5 x)) by (keep_field U1 F2).
  assert (PF2 : Mem.range_perm m2 bp 0 128 Cur Freeable) by (keep_free PF1 F2).
  assert (UF2 : Mem.range_perm m2 bu 0 40 Cur Freeable) by (keep_free UF1 F2).
  assert (SF2 : Mem.range_perm m2 bs 0 40 Cur Freeable) by (keep_free SF1 F2).
  assert (TF2 : Mem.range_perm m2 bt 0 40 Cur Freeable) by (keep_free TF1 F2).
  destruct (exec_mixed_copy_weak_loose e le m2 bp bs true y HA ES EW ltac:(congruence) BY Y2 PF2 SF2)
    as (mc3 & m3 & C4 & C5 & S3 & SF3 & Y3 & PF3 & ValY & BoundY & F3).
  assert (X3 : fe_at m3 bp 0 (words5 x)) by (keep_field X2 F3).
  assert (Z3 : fe_at m3 bp 80 (words5 z)) by (keep_field Z2 F3).
  assert (A3 : fe_at m3 ba 0 (words5 u)) by (keep_field A2 F3).
  assert (B3 : fe_at m3 ba 40 (words5 v)) by (keep_field B2 F3).
  assert (U3 : fe_at m3 bu 0 (words5 x)) by (keep_field U2 F3).
  assert (V3 : fe_at m3 bv 0 (words5 (point_mul_words u t))) by (keep_field V2 F3).
  assert (T3 : fe_at m3 bz 0 (words5 t)) by (keep_field T2 F3).
  assert (AF3 : Mem.range_perm m3 ba 0 88 Cur Freeable) by (keep_free AF2 F3).
  assert (UF3 : Mem.range_perm m3 bu 0 40 Cur Freeable) by (keep_free UF2 F3).
  assert (VF3 : Mem.range_perm m3 bv 0 40 Cur Freeable) by (keep_free VF2 F3).
  assert (TF3 : Mem.range_perm m3 bt 0 40 Cur Freeable) by (keep_free TF2 F3).
  assert (ZF3 : Mem.range_perm m3 bz 0 40 Cur Freeable) by (keep_free ZF2 F3).
  destruct (exec_mixed_s2_calls e le m3 bp ba bt bz v t z HA HB ET EZ EM
    ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)
    BV BT BZ B3 T3 Z3 PF3 AF3 TF3 ZF3)
    as (m4 & mf & C6 & C7 & T4 & B4 & Z4 & PZ4 & PF4 & AF4 & TF4 & ZF4 & ValS & BoundS & F4).
  assert (X4 : fe_at mf bp 0 (words5 x)) by (keep_field X3 F4).
  assert (Y4 : fe_at mf bp 40 (words5 y)) by (keep_field Y3 F4).
  assert (A4 : fe_at mf ba 0 (words5 u)) by (keep_field A3 F4).
  assert (U4 : fe_at mf bu 0 (words5 x)) by (keep_field U3 F4).
  assert (V4 : fe_at mf bv 0 (words5 (point_mul_words u t))) by (keep_field V3 F4).
  assert (S4 : fe_at mf bs 0 (words5 (weak_loose_words y))) by (keep_field S3 F4).
  assert (UF4 : Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_free UF3 F4).
  assert (VF4 : Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_free VF3 F4).
  assert (SF4 : Mem.range_perm mf bs 0 40 Cur Freeable) by (keep_free SF3 F4).
  exists mf;split.
  - unfold mixed_preparation_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc1) (le1:=le);[exact C1|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le);[exact C2|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le);[exact C3|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc3) (le1:=le);[exact C4|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le);[exact C5|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m4) (le1:=le);[exact C6|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le);[exact C7|apply exec_Sskip].
  - split;[exact X4|];split;[exact Y4|];split;[exact PZ4|];split;[exact A4|];split;[exact B4|];
      split;[exact U4|];split;[exact V4|];split;[exact S4|];split;[exact T4|];split;[exact Z4|];
      split;[exact PF4|];split;[exact AF4|];split;[exact UF4|];split;[exact VF4|];split;[exact SF4|];
      split;[exact TF4|];split;[exact ZF4|];split;[exact BoundU|];split;[exact BoundS|].
    eapply lframe_trans.
    + eapply lframe_implies;[exact F1|];intros bx pos (NU & NV & NS & NT & NZ & NP & NA) HV;exact NU.
    + eapply lframe_trans.
      * eapply lframe_implies;[exact F2|];intros bx pos (NU & NV & NS & NT & NZ & NP & NA) HV.
        split;[exact NV|];split;[exact NZ|];cbn [curve_square_offset];destruct NA as [HN|[HN|HN]];[left|right;left|right;right];try assumption;lia.
      * eapply lframe_trans.
        -- eapply lframe_implies;[exact F3|];intros bx pos (NU & NV & NS & NT & NZ & NP & NA) HV;exact NS.
        -- eapply lframe_implies;[exact F4|];intros bx pos (NU & NV & NS & NT & NZ & NP & NA) HV.
           unfold mixed_s2_frame;split;[exact NT|];split;[exact NZ|];split;[|exact NP].
           destruct NA as [HN|[HN|HN]];[left|right;left|right;right];try assumption;lia.
Qed.
