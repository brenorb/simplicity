(** Original negation from affine Y into tmp, then conditional move from tmp
    back to Y. Source/destination offsets and whole-object ownership reflect
    the actual 88-byte point and 40-byte temporary; no repacking is used. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep
  C.jet_sx_revalue_cells C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_local_regions C.jet_secp_field_add_initial C.jet_secp_field_pair_multiply
  C.jet_secp_field_negate_separate C.jet_secp_field_cmov C.jet_secp_field_mul_small
  C.jet_secp_field_point_multiply C.jet_secp_owned_slice_fields C.jet_secp_point_mul_storage
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_curve_frame C.jet_secp_square_columns C.jet_secp_fe_math
  C.jet_secp_b32_exec C.jet_secp_fe_b32 C.jet_secp_closed_helpers
  C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition swu_point_y_regs := mkreg (u64_cells 40 (vars5 0)) true (Some 88).
Definition swu_neg_y_regs := [free_region fe_undef 40;swu_point_y_regs].
Definition swu_neg_y_args := [XP 0 0;XP 1 40;XIc Int.one].
Definition swu_neg_y_state := match xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
  f_secp256k1_fe_negate swu_neg_y_args swu_neg_y_regs [] 5 with
  | Some (RDone st _) => st | _=>mkst (PTree.empty sx) [] [] 0 end.
Definition swu_neg_y_out_regs := [mkreg (u64_cells 0 negate_sep_out) true (Some 40);swu_point_y_regs].
Definition swu_y_frame (bt bp b:block) pos := b<>bt /\ (b<>bp \/ pos<40 \/ 80<=pos).
Lemma swu_neg_y_run : xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
  f_secp256k1_fe_negate swu_neg_y_args swu_neg_y_regs [] 5=Some (RDone swu_neg_y_state ONormal).
Proof. vm_compute;reflexivity. Qed.
Lemma swu_neg_y_return : (stemps swu_neg_y_state)!1%positive=None.
Proof. vm_compute;reflexivity. Qed.
Lemma swu_neg_y_output : sregs swu_neg_y_state=swu_neg_y_out_regs.
Proof. vm_compute;reflexivity. Qed.
Lemma swu_y_cell_range xs d ch : length xs=5%nat ->
  In (d,ch) (map cshape (u64_cells 40 xs)) -> 40<=d /\ d+size_chunk ch<=80.
Proof.
  intros Len Member;apply in_map_iff in Member;destruct Member as [cell [Eq Member]].
  destruct (u64_cells_In xs 40 cell Member) as (i & x & Nth & ->).
  cbn [cshape cofs cchunk] in Eq;injection Eq as <- <-.
  assert (Index:(i<5)%nat) by (rewrite <-Len;apply nth_error_Some;rewrite Nth;discriminate).
  change (40<=40+8*Z.of_nat i /\ 40+8*Z.of_nat i+8<=80).
  pose proof (Nat2Z.is_nonneg i);lia.
Qed.
Lemma swu_neg_y_initial w m bt bp : bt<>bp -> Mem.range_perm m bt 0 40 Cur Freeable ->
  fe_at m bp 40 (words5 w) -> Mem.range_perm m bp 0 88 Cur Freeable ->
  rep w [(bt,0);(bp,0)] swu_neg_y_regs m.
Proof.
  intros Ne FT Y FP;apply two_region_rep_separate;[reflexivity|exact Ne| |].
  - apply region_with_freeable.
    + apply region_fe_undefined_from_storage;cbn [bas blk lay nth fst snd];
        [lia|exists 0;reflexivity|change (40<=18446744073709551615);lia|
         apply freeable_range_writable;exact FT].
    + reflexivity.
    + reflexivity.
    + exact FT.
    + apply fe_undef_storage_size.
  - apply (owned_field_values_slice_region w [(bt,0);(bp,0)] m 1 0 40 88);
      [reflexivity|lia|lia|exact Y|exact FP].
Qed.

Theorem eval_swu_negate_y w m bt bp : bt<>bp -> mul_small_input_bounds w ->
  Mem.range_perm m bt 0 40 Cur Freeable -> fe_at m bp 40 (words5 w) ->
  Mem.range_perm m bp 0 88 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr bt Ptrofs.zero;Vptr bp (Ptrofs.repr 40);Vint Int.one] E0 mf Vundef /\
  fe_at mf bt 0 (words5 (negate_sep_words w)) /\ fe_at mf bp 40 (words5 w) /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bp 0 88 Cur Freeable /\
  radix_value (negate_sep_words w)=4*feP-radix_value w /\ square_input_bounds (negate_sep_words w) /\
  lframe (swu_y_frame bt bp) m mf /\ readonly_preserved m mf.
Proof.
  intros Ne Bounds FT Y FP.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 160 f_secp256k1_fe_negate
    swu_neg_y_args swu_neg_y_regs 5 _ swu_neg_y_run eq_refl w [(bt,0);(bp,0)] m
    (swu_neg_y_initial w m bt bp Ne FT Y FP))
    as (mf & result & Call & Rep & Ret & Shape & Frame).
  cbn [rsel fst] in Rep,Ret;rewrite swu_neg_y_return in Ret;subst result.
  change (map (den w (lay [(bt,0);(bp,0)])) swu_neg_y_args) with
    [Vptr bt Ptrofs.zero;Vptr bp (Ptrofs.repr 40);Vint Int.one] in Call.
  rewrite swu_neg_y_output in Rep.
  pose proof (rep_region _ _ _ _ 0 _ Rep eq_refl) as R0.
  pose proof (rep_region _ _ _ _ 1 _ Rep eq_refl) as R1.
  pose proof R0 as (_ & _ & _ & _ & _ & _ & FTF & _).
  pose proof R1 as (_ & _ & _ & _ & _ & _ & FPF & _).
  assert (Out:fe_at mf bt 0 (words5 (negate_sep_words w))).
  { eapply owned_region_field_slice with (rho:=w) (beta:=[(bt,0);(bp,0)]) (r:=0%nat)
      (size:=40) (exprs:=negate_sep_out);
      [exact R0|lia|exists 0;reflexivity|lia|change (40<=18446744073709551615);lia|
       reflexivity|reflexivity|intros;assumption|apply negate_sep_output_den]. }
  assert (Source:fe_at mf bp 40 (words5 w)).
  { eapply owned_region_field_slice with (rho:=w) (beta:=[(bt,0);(bp,0)]) (r:=1%nat)
      (size:=88) (exprs:=vars5 0);
      [exact R1|lia|exists 5;reflexivity|lia|change (88<=18446744073709551615);lia|
       reflexivity|reflexivity|intros;assumption|reflexivity]. }
  destruct (negate_sep_numeric w Bounds) as [Value OutBounds].
  exists mf;split;[exact Call|];split;[exact Out|];split;[exact Source|];split;[exact FTF|];
    split;[exact FPF|];split;[exact Value|];split;[exact OutBounds|];split.
  - eapply lframe_implies;[exact Frame|];intros b pos [NT Outside] Valid
      (r & sh & d & ch & Nth & Cell & Block & Range).
    destruct r as [|[|r]];try discriminate Nth.
    + cbn [bas blk lay nth fst] in Block;contradiction.
    + injection Nth as <-.
      change (In (d,ch) (map cshape (u64_cells 40 (vars5 0)))) in Cell.
      destruct (swu_y_cell_range (vars5 0) d ch eq_refl Cell) as [Lo Hi].
      cbn [bas blk lay nth fst snd] in Block,Range;destruct Outside as [NP|[Low|High]];
        [contradiction|lia|lia].
    + destruct r;discriminate Nth.
  - eapply (secp_closed_function_preserved f_secp256k1_fe_negate);[reflexivity|reflexivity|exact Call].
Qed.

Definition swu_cmov_y_regs := [swu_point_y_regs;free_region (fe_reg (vars5 5)) 40].
Definition swu_cmov_y_args flag := [XP 0 40;XP 1 0;XI (cmov_int flag)].
Definition swu_cmov_y_state flag := match xfun (genv_cenv secp_ge) [] (int_table secp_pure) 96
  f_secp256k1_fe_cmov (swu_cmov_y_args flag) swu_cmov_y_regs [] 10 with
  | Some (RDone st _) => st | _=>mkst (PTree.empty sx) [] [] 0 end.
Definition swu_cmov_y_out_regs flag :=
  [mkreg (u64_cells 40 (cmov_out flag)) true (Some 88);free_region (fe_reg (vars5 5)) 40].
Lemma swu_cmov_y_run flag : xfun (genv_cenv secp_ge) [] (int_table secp_pure) 96
  f_secp256k1_fe_cmov (swu_cmov_y_args flag) swu_cmov_y_regs [] 10=
  Some (RDone (swu_cmov_y_state flag) ONormal).
Proof. destruct flag;vm_compute;reflexivity. Qed.
Lemma swu_cmov_y_return flag : (stemps (swu_cmov_y_state flag))!1%positive=None.
Proof. destruct flag;vm_compute;reflexivity. Qed.
Lemma swu_cmov_y_output flag : sregs (swu_cmov_y_state flag)=swu_cmov_y_out_regs flag.
Proof. destruct flag;vm_compute;reflexivity. Qed.
Lemma swu_cmov_y_initial a b m bp bt : bp<>bt ->
  fe_at m bp 40 (words5 a) -> fe_at m bt 0 (words5 b) ->
  Mem.range_perm m bp 0 88 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  rep (field_pair_valuation a b) [(bp,0);(bt,0)] swu_cmov_y_regs m.
Proof.
  intros Ne A B FP FT;apply two_region_rep_separate;[reflexivity|exact Ne| |].
  - apply (owned_field_values_slice_region (field_pair_valuation a b) [(bp,0);(bt,0)] m 0 0 40 88);
      [reflexivity|lia|lia|rewrite field_pair_left;exact A|exact FP].
  - apply (owned_field_values_slice_region (field_pair_valuation a b) [(bp,0);(bt,0)] m 1 5 0 40);
      [reflexivity|lia|lia|rewrite field_pair_right;exact B|exact FT].
Qed.
Theorem eval_swu_cmov_y flag a b m bp bt : bp<>bt ->
  fe_at m bp 40 (words5 a) -> fe_at m bt 0 (words5 b) ->
  Mem.range_perm m bp 0 88 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_cmov)
    [Vptr bp (Ptrofs.repr 40);Vptr bt Ptrofs.zero;Vint (cmov_int flag)] E0 mf Vundef /\
  fe_at mf bp 40 (words5 (if flag then b else a)) /\ fe_at mf bt 0 (words5 b) /\
  Mem.range_perm mf bp 0 88 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  lframe (swu_y_frame bt bp) m mf /\ readonly_preserved m mf.
Proof.
  intros Ne A B FP FT.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 96 f_secp256k1_fe_cmov
    (swu_cmov_y_args flag) swu_cmov_y_regs 10 _ (swu_cmov_y_run flag) eq_refl
    (field_pair_valuation a b) [(bp,0);(bt,0)] m (swu_cmov_y_initial a b m bp bt Ne A B FP FT))
    as (mf & result & Call & Rep & Ret & Shape & Frame).
  cbn [rsel fst] in Rep,Ret;rewrite swu_cmov_y_return in Ret;subst result.
  change (map (den (field_pair_valuation a b) (lay [(bp,0);(bt,0)])) (swu_cmov_y_args flag)) with
    [Vptr bp (Ptrofs.repr 40);Vptr bt Ptrofs.zero;Vint (cmov_int flag)] in Call.
  rewrite swu_cmov_y_output in Rep.
  pose proof (rep_region _ _ _ _ 0 _ Rep eq_refl) as R0.
  pose proof (rep_region _ _ _ _ 1 _ Rep eq_refl) as R1.
  pose proof R0 as (_ & _ & _ & _ & _ & _ & FPF & _).
  pose proof R1 as (_ & _ & _ & _ & _ & _ & FTF & _).
  assert (Out:fe_at mf bp 40 (words5 (if flag then b else a))).
  { eapply owned_region_field_slice with (rho:=field_pair_valuation a b) (beta:=[(bp,0);(bt,0)]) (r:=0%nat)
      (size:=88) (exprs:=cmov_out flag);
      [exact R0|lia|exists 5;reflexivity|lia|change (88<=18446744073709551615);lia|
       reflexivity|reflexivity|intros;assumption|apply cmov_out_den]. }
  assert (Source:fe_at mf bt 0 (words5 b)).
  { eapply owned_region_field_slice with (rho:=field_pair_valuation a b) (beta:=[(bp,0);(bt,0)]) (r:=1%nat)
      (size:=40) (exprs:=vars5 5);
      [exact R1|lia|exists 0;reflexivity|lia|change (40<=18446744073709551615);lia|
       reflexivity|reflexivity|intros;assumption|reflexivity]. }
  exists mf;split;[exact Call|];split;[exact Out|];split;[exact Source|];
    split;[exact FPF|];split;[exact FTF|];split.
  - eapply lframe_implies;[exact Frame|];intros bi pos [NT Outside] Valid
      (r & sh & d & ch & Nth & Cell & Block & Range).
    destruct r as [|[|r]];try discriminate Nth.
    + injection Nth as <-.
      change (In (d,ch) (map cshape (u64_cells 40 (cmov_out flag)))) in Cell.
      destruct (swu_y_cell_range (cmov_out flag) d ch eq_refl Cell) as [Lo Hi].
      cbn [bas blk lay nth fst snd] in Block,Range;destruct Outside as [NP|[Low|High]];
        [contradiction|lia|lia].
    + cbn [bas blk lay nth fst] in Block;contradiction.
    + destruct r;discriminate Nth.
  - eapply (secp_closed_function_preserved f_secp256k1_fe_cmov);[exact cmov_closed|reflexivity|exact Call].
Qed.
