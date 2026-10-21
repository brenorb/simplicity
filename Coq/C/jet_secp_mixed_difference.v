(** The original negate/add pairs preparing H and I, shared through their
    actual local identifiers. Machine execution is derived from owned fields. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_field_negate_separate C.jet_secp_field_negate_values C.jet_secp_field_mul_small
  C.jet_secp_field_add_scaled C.jet_secp_field_sum_bounds C.jet_secp_field_sum_owned C.jet_secp_square_columns
  C.jet_secp_curve_statements C.jet_secp_mixed_s2_calls C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_statement_prefix.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_difference_words a b := field_sum_words (negate_sep_words a) b.
Definition mixed_diff_negate (i : bool) := curve_call _secp256k1_fe_negate f_secp256k1_fe_negate None
  [curve_local_address (if i then _i else _h);curve_local_address (if i then _s2 else _u1);
   Econst_int Int.one tint].
Definition mixed_diff_add (i : bool) := curve_call _secp256k1_fe_add f_secp256k1_fe_add None
  [curve_local_address (if i then _i else _h);curve_local_address (if i then _s1 else _u2)].
Definition mixed_after_difference := match mixed_after_s2_z with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ rest))) => rest | _ => Sskip end.
Lemma mixed_difference_source : mixed_after_s2_z=
  Ssequence (mixed_diff_negate false) (Ssequence (mixed_diff_add false)
    (Ssequence (mixed_diff_negate true) (Ssequence (mixed_diff_add true) mixed_after_difference))).
Proof. reflexivity. Qed.

Lemma mixed_negate_scaled w : mul_small_input_bounds w -> field_scaled_bounds 4 (negate_sep_words w).
Proof.
  intros HB i HI;rewrite negate_sep_unsigned by assumption.
  pose proof (Int64.unsigned_range_2 (w i)).
  destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb negate_mask];lia.
Qed.
Lemma mixed_difference_numeric a b : mul_small_input_bounds a -> mul_small_input_bounds b ->
  radix_value (mixed_difference_words a b)=4*feP-radix_value a+radix_value b /\
  square_input_bounds (mixed_difference_words a b).
Proof.
  intros BA BB;pose proof (mixed_negate_scaled a BA) as BN;pose proof (field_tight_scaled b BB) as BP.
  split.
  - unfold mixed_difference_words;rewrite (field_sum_exact_value _ _
      (field_sum_scaled_no_overflow 4 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) BN BP)).
    rewrite (proj1 (negate_sep_numeric a BA));reflexivity.
  - apply (field_scaled_loose 5 _ ltac:(lia)).
    exact (field_sum_scaled_bounds 4 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) BN BP).
Qed.

Theorem exec_mixed_difference (i : bool) a b e le m bo bm bp :
  e!(if i then _i else _h)=Some (bo,curve_fe_type) ->
  e!(if i then _s2 else _u1)=Some (bm,curve_fe_type) -> e!(if i then _s1 else _u2)=Some (bp,curve_fe_type) ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
  mul_small_input_bounds a -> mul_small_input_bounds b -> bo<>bm -> bo<>bp -> bm<>bp ->
  fe_at m bm 0 (words5 a) -> fe_at m bp 0 (words5 b) ->
  Mem.range_perm m bo 0 40 Cur Freeable -> Mem.range_perm m bm 0 40 Cur Freeable -> Mem.range_perm m bp 0 40 Cur Freeable ->
  exists mn mf,
  Clight2.exec_stmt secp_ge e le m (mixed_diff_negate i) E0 le mn Out_normal /\
  Clight2.exec_stmt secp_ge e le mn (mixed_diff_add i) E0 le mf Out_normal /\
  fe_at mf bo 0 (words5 (mixed_difference_words a b)) /\
  fe_at mf bm 0 (words5 a) /\ fe_at mf bp 0 (words5 b) /\
  Mem.range_perm mf bo 0 40 Cur Freeable /\ Mem.range_perm mf bm 0 40 Cur Freeable /\ Mem.range_perm mf bp 0 40 Cur Freeable /\
  radix_value (mixed_difference_words a b)=4*feP-radix_value a+radix_value b /\
  square_input_bounds (mixed_difference_words a b) /\ lframe (fun bx _=>bx<>bo /\ bx<>bm /\ bx<>bp) m mf.
Proof.
  intros EO EM EP EN EA BA BB HOM HOP HMP A B OF MF PF.
  destruct (eval_negate_sep_from_storage a m bo bm BA HOM OF A MF)
    as (mn & CN & N & A1 & OF1 & MF1 & VN & BN & FN).
  pose proof (field_at_lframe m mn bp 0 _ _ B FN ltac:(intro pos;split;congruence)) as B1.
  pose proof (curve_keep_free _ m mn bp 40 ltac:(lia) PF FN ltac:(intro pos;split;congruence)) as PF1.
  destruct (eval_field_sum_owned (negate_sep_words a) b mn bo bp HOP N B1 OF1 PF1)
    as (mf & CA & O2 & B2 & OF2 & PF2 & FA).
  pose proof (field_at_lframe mn mf bm 0 _ _ A1 FA ltac:(intro pos;split;congruence)) as A2.
  pose proof (curve_keep_free _ mn mf bm 40 ltac:(lia) MF1 FA ltac:(intro pos;split;congruence)) as MF2.
  destruct (mixed_difference_numeric a b BA BB) as (Val & Bound).
  exists mn,mf;split.
  - unfold mixed_diff_negate;eapply exec_curve_call with
      (vargs:=[Vptr bo Ptrofs.zero;Vptr bm Ptrofs.zero;Vint Int.one]) (v:=Vundef).
    + unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
    + exact EN.
    + eapply eval_Econs;[apply eval_curve_local;exact EO|reflexivity|].
      eapply eval_Econs;[apply eval_curve_local;exact EM|reflexivity|].
      eapply eval_Econs;[constructor|reflexivity|constructor].
    + exact CN.
  - split.
    + unfold mixed_diff_add;eapply exec_curve_call with (vargs:=[Vptr bo Ptrofs.zero;Vptr bp Ptrofs.zero]) (v:=Vundef).
      * unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
      * exact EA.
      * eapply eval_Econs;[apply eval_curve_local;exact EO|reflexivity|].
        eapply eval_Econs;[apply eval_curve_local;exact EP|reflexivity|constructor].
      * exact CA.
    + split;[exact O2|];split;[exact A2|];split;[exact B2|];split;[exact OF2|];split;[exact MF2|];
        split;[exact PF2|];split;[exact Val|];split;[exact Bound|].
      eapply lframe_trans.
      * eapply lframe_implies;[exact FN|];intros bx pos (NO & NM & NP) HV;split;assumption.
      * eapply lframe_implies;[exact FA|];intros bx pos (NO & NM & NP) HV;split;assumption.
Qed.

Definition mixed_difference_statements :=
  [mixed_diff_negate false;mixed_diff_add false;mixed_diff_negate true;mixed_diff_add true].
Lemma mixed_differences_source : mixed_after_s2_z=
  statement_sequence mixed_difference_statements mixed_after_difference.
Proof. reflexivity. Qed.

Local Ltac separate_difference_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by tauto;assert (HQ : ~Q) by tauto;clear HS end.
Local Ltac preserve_diff_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac preserve_diff_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.

Theorem exec_mixed_differences e le m bh bi bu bv bs bt x u y s :
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> NoDup [bh;bi;bu;bv;bs;bt] ->
  mul_small_input_bounds x -> mul_small_input_bounds u -> mul_small_input_bounds y -> mul_small_input_bounds s ->
  fe_at m bu 0 (words5 x) -> fe_at m bv 0 (words5 u) -> fe_at m bs 0 (words5 y) -> fe_at m bt 0 (words5 s) ->
  Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_difference_statements Sskip) E0 le mf Out_normal /\
  fe_at mf bh 0 (words5 (mixed_difference_words x u)) /\ fe_at mf bi 0 (words5 (mixed_difference_words s y)) /\
  fe_at mf bu 0 (words5 x) /\ fe_at mf bv 0 (words5 u) /\ fe_at mf bs 0 (words5 y) /\ fe_at mf bt 0 (words5 s) /\
  Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  radix_value (mixed_difference_words x u)=4*feP-radix_value x+radix_value u /\
  radix_value (mixed_difference_words s y)=4*feP-radix_value s+radix_value y /\
  square_input_bounds (mixed_difference_words x u) /\ square_input_bounds (mixed_difference_words s y) /\
  lframe (fun bx _=>bx<>bh /\ bx<>bi /\ bx<>bu /\ bx<>bv /\ bx<>bs /\ bx<>bt) m mf.
Proof.
  intros EH EI EU EV ES ET EN EA Sep BX BU BY BS X U Y S HF IF UF VF SF TF.
  separate_difference_blocks Sep.
  destruct (exec_mixed_difference false x u e le m bh bu bv EH EU EV EN EA BX BU
    ltac:(congruence) ltac:(congruence) ltac:(congruence) X U HF UF VF)
    as (mn & m1 & C1 & C2 & H1 & X1 & U1 & HF1 & UF1 & VF1 & ValH & BoundH & F1).
  assert (Y1 : fe_at m1 bs 0 (words5 y)) by (preserve_diff_field Y F1).
  assert (S1 : fe_at m1 bt 0 (words5 s)) by (preserve_diff_field S F1).
  assert (IF1 : Mem.range_perm m1 bi 0 40 Cur Freeable) by (preserve_diff_free IF F1).
  assert (SF1 : Mem.range_perm m1 bs 0 40 Cur Freeable) by (preserve_diff_free SF F1).
  assert (TF1 : Mem.range_perm m1 bt 0 40 Cur Freeable) by (preserve_diff_free TF F1).
  destruct (exec_mixed_difference true s y e le m1 bi bt bs EI ET ES EN EA BS BY
    ltac:(congruence) ltac:(congruence) ltac:(congruence) S1 Y1 IF1 TF1 SF1)
    as (mi & mf & C3 & C4 & I2 & S2 & Y2 & IF2 & TF2 & SF2 & ValI & BoundI & F2).
  assert (H2 : fe_at mf bh 0 (words5 (mixed_difference_words x u))) by (preserve_diff_field H1 F2).
  assert (X2 : fe_at mf bu 0 (words5 x)) by (preserve_diff_field X1 F2).
  assert (U2 : fe_at mf bv 0 (words5 u)) by (preserve_diff_field U1 F2).
  assert (HF2 : Mem.range_perm mf bh 0 40 Cur Freeable) by (preserve_diff_free HF1 F2).
  assert (UF2 : Mem.range_perm mf bu 0 40 Cur Freeable) by (preserve_diff_free UF1 F2).
  assert (VF2 : Mem.range_perm mf bv 0 40 Cur Freeable) by (preserve_diff_free VF1 F2).
  exists mf;split.
  - unfold mixed_difference_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le);[exact C1|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le);[exact C2|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le);[exact C3|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le);[exact C4|apply exec_Sskip].
  - split;[exact H2|];split;[exact I2|];split;[exact X2|];split;[exact U2|];split;[exact Y2|];split;[exact S2|];
      split;[exact HF2|];split;[exact IF2|];split;[exact UF2|];split;[exact VF2|];split;[exact SF2|];split;[exact TF2|];
      split;[exact ValH|];split;[exact ValI|];split;[exact BoundH|];split;[exact BoundI|].
    eapply lframe_trans.
    + eapply lframe_implies;[exact F1|];intros bx pos (NH & NI & NU & NV & NS & NT) HV;repeat split;assumption.
    + eapply lframe_implies;[exact F2|];intros bx pos (NH & NI & NU & NV & NS & NT) HV;repeat split;assumption.
Qed.
