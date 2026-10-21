(** Original finite mixed-addition preparation: flag checks, square and all
    U/S fields. Execution and ownership come from initial storage, not calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_curve_square C.jet_secp_point_write_run
  C.jet_secp_curve_statements C.jet_secp_mixed_finite_start C.jet_secp_mixed_copy_weak
  C.jet_secp_mixed_affine_product C.jet_secp_mixed_s2_calls C.jet_secp_field_weak_tight
  C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_statement_prefix
  C.jet_secp_mixed_head C.jet_secp_double_statements C.jet_secp_point_square_coordinate C.jet_secp_square_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words.

Definition mixed_preparation_statements :=
  [mixed_copy_coordinate false;mixed_weak_coordinate false;mixed_affine_call false;
   mixed_copy_coordinate true;mixed_weak_coordinate true;mixed_affine_call true;mixed_s2_z_call].
Definition mixed_prepare_frame (bp ba bu bv bs bt bz bx : block) (pos : Z) :=
  bx<>bu /\ bx<>bv /\ bx<>bs /\ bx<>bt /\ bx<>bz /\
  (bx<>bp \/ pos<80 \/ 120<=pos) /\ (bx<>ba \/ pos<0 \/ 80<=pos).
Lemma mixed_preparation_source : mixed_after_square=
  statement_sequence mixed_preparation_statements mixed_after_s2_z.
Proof. reflexivity. Qed.

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

Theorem exec_mixed_preparation e le m bp ba bu bv bs bt bz x y z u v t :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None ->
  NoDup [bp;ba;bu;bv;bs;bt;bz] ->
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
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
  fe_at mf bs 0 (words5 y) /\ fe_at mf bt 0 (words5 (point_mul_words (point_mul_words v t) z)) /\
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
  destruct (exec_mixed_copy_weak e le m2 bp bs true y HA ES EW ltac:(congruence) BY Y2 PF2 SF2)
    as (mc3 & m3 & C4 & C5 & S3 & SF3 & Y3 & PF3 & F3).
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
  assert (S4 : fe_at mf bs 0 (words5 y)) by (keep_field S3 F4).
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

Lemma exec_mixed_preparation_then_rest e le m mp mf le' out :
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_preparation_statements Sskip) E0 le mp Out_normal ->
  Clight2.exec_stmt secp_ge e le mp mixed_after_s2_z E0 le' mf out ->
  Clight2.exec_stmt secp_ge e le m mixed_after_square E0 le' mf out.
Proof.
  intros HP HT;rewrite mixed_preparation_source;eapply exec_statement_prefix_then_last;eassumption.
Qed.

Definition mixed_finite_preparation_statements :=
  [mixed_head;mixed_b_head;mixed_square_stmt]++mixed_preparation_statements.
Definition mixed_preparation_temps le := PTree.set _t'3 (Vint Int.zero) (PTree.set _t'4 (Vint Int.zero) le).
Lemma mixed_finite_preparation_source : fn_body f_secp256k1_gej_add_ge_var=
  statement_sequence mixed_finite_preparation_statements mixed_after_s2_z.
Proof. reflexivity. Qed.

Theorem exec_mixed_finite_preparation e le m bp ba bu bv bs bt bz x y z u v :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  NoDup [bp;ba;bu;bv;bs;bt;bz] ->
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
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_finite_preparation_statements Sskip) E0
    (mixed_preparation_temps le) mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 z) /\
  fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\
  fe_at mf bu 0 (words5 x) /\ fe_at mf bv 0 (words5 (point_mul_words u (square_words z))) /\
  fe_at mf bs 0 (words5 y) /\ fe_at mf bt 0 (words5 (point_mul_words (point_mul_words v (square_words z)) z)) /\
  fe_at mf bz 0 (words5 (square_words z)) /\
  Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\ Mem.load Mint32 mf ba 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
  square_input_bounds (square_words z) /\ square_input_bounds (point_mul_words u (square_words z)) /\
  square_input_bounds (point_mul_words (point_mul_words v (square_words z)) z) /\
  lframe (mixed_prepare_frame bp ba bu bv bs bt bz) m mf.
Proof.
  intros HA HB EU EV ES ET EZ EW EM EQ Sep FlagA FlagB BX BY BZ BU BV X Y Z U V PF AF UF VF SF TF ZF.
  pose proof Sep as Sep0;separate_blocks Sep.
  destruct (eval_point_square_coordinate PointZ z m bz bp BZ ZF Z PF ltac:(congruence))
    as (mi & C0 & Z0 & ZF0 & PZ0 & PF0 & ValZ & BoundZ & TightZ & RawFrame0).
  assert (F0 : lframe (fun bx pos=>bx<>bz /\ (bx<>bp \/ pos<80 \/ 120<=pos)) m mi).
  { eapply lframe_implies;[exact RawFrame0|];intros bx pos (NZ & NP) HV.
    unfold point_square_coordinate_frame;intros [[HE HR]|[HE HR]];[contradiction|].
    subst bx;change (80<=pos<120) in HR;destruct NP as [HN|[HN|HN]];[contradiction|lia|lia]. }
  assert (X0 : fe_at mi bp 0 (words5 x)) by (keep_field X F0).
  assert (Y0 : fe_at mi bp 40 (words5 y)) by (keep_field Y F0).
  assert (U0 : fe_at mi ba 0 (words5 u)) by (keep_field U F0).
  assert (V0 : fe_at mi ba 40 (words5 v)) by (keep_field V F0).
  assert (AF0 : Mem.range_perm mi ba 0 88 Cur Freeable) by (keep_free AF F0).
  assert (UF0 : Mem.range_perm mi bu 0 40 Cur Freeable) by (keep_free UF F0).
  assert (VF0 : Mem.range_perm mi bv 0 40 Cur Freeable) by (keep_free VF F0).
  assert (SF0 : Mem.range_perm mi bs 0 40 Cur Freeable) by (keep_free SF F0).
  assert (TF0 : Mem.range_perm mi bt 0 40 Cur Freeable) by (keep_free TF F0).
  assert (HA' : (mixed_preparation_temps le)!_a=Some (Vptr bp Ptrofs.zero)).
  { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HA. }
  assert (HB' : (mixed_preparation_temps le)!_b=Some (Vptr ba Ptrofs.zero)).
  { unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HB. }
  destruct (exec_mixed_preparation e (mixed_preparation_temps le) mi bp ba bu bv bs bt bz
    x y z u v (square_words z) HA' HB' EU EV ES ET EZ EW EM Sep0 BX BY BZ BU BV BoundZ
    X0 Y0 PZ0 U0 V0 Z0 PF0 AF0 UF0 VF0 SF0 TF0 ZF0)
    as (mf & HP & XO & YO & ZO & AO & BO & UO & VO & SO & TO & Z12O & PFO & AFO & UFO & VFO & SFO & TFO & ZFO & BoundU & BoundS & Frame).
  assert (FrameTotal : lframe (mixed_prepare_frame bp ba bu bv bs bt bz) m mf).
  { eapply lframe_trans;[|exact Frame].
    eapply lframe_implies;[exact F0|];intros bx pos (NU & NV & NS & NT & NZ & NP & NA) HV.
    split;assumption. }
  assert (FlagAO : Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FrameTotal Mint32 bp 120).
    - exact FlagA.
    - eapply Mem.perm_valid_block;apply (PF 0);lia.
    - intros pos HP';geometry ltac:(clear - HP';change (120<=pos<124) in HP';lia). }
  assert (FlagBO : Mem.load Mint32 mf ba 80=Some (Vint Int.zero)).
  { rewrite (proj1 FrameTotal Mint32 ba 80).
    - exact FlagB.
    - eapply Mem.perm_valid_block;apply (AF 0);lia.
    - intros pos HP';geometry ltac:(clear - HP';change (80<=pos<84) in HP';lia). }
  exists mf;split.
  - unfold mixed_finite_preparation_statements;cbn [app statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint Int.zero) le).
    + apply exec_mixed_head_finite with (ba:=bp);assumption.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=mixed_preparation_temps le).
      * apply exec_mixed_b_head_finite with (bb:=ba);[rewrite PTree.gso by discriminate;exact HB|exact FlagB].
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=mixed_preparation_temps le).
        -- unfold mixed_square_stmt;eapply exec_curve_call with
             (vargs:=[Vptr bz Ptrofs.zero;Vptr bp (Ptrofs.repr 80)]) (v:=Vundef).
           ++ unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
           ++ exact EQ.
           ++ eapply eval_Econs;[apply eval_curve_local;exact EZ|reflexivity|].
              eapply eval_Econs with (v1:=Vptr bp (Ptrofs.repr 80));
                [apply eval_double_point_address;[cbn [In];tauto|exact HA']|reflexivity|constructor].
           ++ exact C0.
        -- exact HP.
  - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact AO|];split;[exact BO|];
      split;[exact UO|];split;[exact VO|];split;[exact SO|];split;[exact TO|];split;[exact Z12O|];
      split;[exact FlagAO|];split;[exact FlagBO|];
      split;[exact PFO|];split;[exact AFO|];split;[exact UFO|];split;[exact VFO|];split;[exact SFO|];
      split;[exact TFO|];split;[exact ZFO|];split;[exact BoundZ|];split;[exact BoundU|];split;[exact BoundS|].
    exact FrameTotal.
Qed.
