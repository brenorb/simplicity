(** Original in-place equal-point mixed addition with separate ratio storage,
    including its ten actual local allocations and frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
  C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_mixed_function
  C.jet_secp_mixed_equal_ratio C.jet_secp_mixed_finite_return C.jet_secp_mixed_preparation
  C.jet_secp_double_all_calls C.jet_secp_double_var_owned C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_ratio_entry_temps bp ba br := PTree.set _rzr (Vptr br Ptrofs.zero) (mixed_entry_temps bp ba).
Lemma mixed_ratio_function_entry m m1 m2 m3 m4 m5 m6 m7 m8 m9 mi bp ba br bz bu bv bs bt bh bi b2 b3 bk :
  Mem.alloc m 0 40=(m1,bz) -> Mem.alloc m1 0 40=(m2,bu) -> Mem.alloc m2 0 40=(m3,bv) ->
  Mem.alloc m3 0 40=(m4,bs) -> Mem.alloc m4 0 40=(m5,bt) -> Mem.alloc m5 0 40=(m6,bh) ->
  Mem.alloc m6 0 40=(m7,bi) -> Mem.alloc m7 0 40=(m8,b2) -> Mem.alloc m8 0 40=(m9,b3) -> Mem.alloc m9 0 40=(mi,bk) ->
  function_entry2 secp_ge f_secp256k1_gej_add_ge_var
    [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br Ptrofs.zero] m
    (mixed_helper_env bz bu bv bs bt bh bi b2 b3 bk) (mixed_ratio_entry_temps bp ba br) mi.
Proof.
  intros AZ AU AV AS AT AH AI A2 A3 AK.
  pose proof (mixed_function_entry m m1 m2 m3 m4 m5 m6 m7 m8 m9 mi bp ba bz bu bv bs bt bh bi b2 b3 bk
    AZ AU AV AS AT AH AI A2 A3 AK) as Entry.
  inversion Entry;subst;constructor;try assumption;reflexivity.
Qed.

Local Ltac allocated_valid := first [assumption |
  match goal with A : Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
    eapply Mem.valid_new_block;exact A end |
  match goal with A : Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
    eapply Mem.valid_block_alloc;[exact A|allocated_valid] end].
Local Ltac allocated_distinct := first [assumption |
  match goal with A : Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
    let HE := fresh "HE" in intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ A);rewrite <-HE;allocated_valid end |
  match goal with A : Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
    let HE := fresh "HE" in intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ A);rewrite HE;allocated_valid end].
Local Ltac allocated_perm HP := first [
  match goal with A : Mem.alloc _ _ _=(?mm,?bb) |- Mem.perm ?mm ?bb _ _ _ =>
    eapply Mem.perm_alloc_2;[exact A|exact HP] end |
  match goal with A : Mem.alloc _ _ _=(?mm,_) |- Mem.perm ?mm _ _ _ _ =>
    eapply Mem.perm_alloc_1;[exact A|allocated_perm HP] end].
Local Ltac allocated_frame :=
  lazymatch goal with |- lframe _ ?ma ?mb =>
    tryif constr_eq ma mb then apply lframe_refl else
    match goal with A : Mem.alloc ma _ _=(?mi,_) |- _ =>
      eapply lframe_trans with (m2:=mi);
        [apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact A|allocated_frame] end end.
Local Ltac separate_ratio_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.

Theorem eval_mixed_equal_ratio_function x y z u v m bp ba br :
  NoDup [bp;ba;br] ->
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
  radix_value (mixed_h_words x z u) mod feP=0 -> radix_value (mixed_i_words y z v) mod feP=0 ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m br 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_ge_var)
    [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bp 0 (words5 (double_output_x_words x y)) /\
  fe_at mf bp 40 (words5 (double_output_y_words x y)) /\
  fe_at mf bp 80 (words5 (double_output_z_words y z)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (double_var_zflag y z)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  square_input_bounds (double_output_x_words x y) /\
  square_input_bounds (double_output_y_words x y) /\
  square_input_bounds (double_output_z_words y z) /\
  fe_at mf br 0 (words5 y) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun b _=>b<>bp /\ b<>ba /\ b<>br) m mf.
Proof.
  intros SepIn BX BY BZ BU BV H0 I0 FlagA FlagB X Y Z U V PF AF RF.
  separate_ratio_blocks SepIn.
  assert (HVP : Mem.valid_block m bp) by (eapply Mem.perm_valid_block;apply (PF 0);lia).
  assert (HVA : Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (AF 0);lia).
  assert (HVR : Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (RF 0);lia).
  destruct (Mem.alloc m 0 40) as (m1 & bz) eqn:AZ.
  destruct (Mem.alloc m1 0 40) as (m2 & bu) eqn:AU.
  destruct (Mem.alloc m2 0 40) as (m3 & bv) eqn:AV.
  destruct (Mem.alloc m3 0 40) as (m4 & bs) eqn:AS.
  destruct (Mem.alloc m4 0 40) as (m5 & bt) eqn:AT.
  destruct (Mem.alloc m5 0 40) as (m6 & bh) eqn:AH.
  destruct (Mem.alloc m6 0 40) as (m7 & bi) eqn:AI.
  destruct (Mem.alloc m7 0 40) as (m8 & b2) eqn:A2.
  destruct (Mem.alloc m8 0 40) as (m9 & b3) eqn:A3.
  destruct (Mem.alloc m9 0 40) as (mi & bk) eqn:AK.
  assert (SepAll : NoDup [bp;ba;br;bu;bv;bs;bt;bz;bh;bi;b2;b3;bk]).
  { repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
      repeat split;try apply NoDup_nil;try apply in_nil;first [congruence|allocated_distinct]. }
  assert (Old : forall b, Mem.valid_block m b ->
    b<>bz /\ b<>bu /\ b<>bv /\ b<>bs /\ b<>bt /\ b<>bh /\ b<>bi /\ b<>b2 /\ b<>b3 /\ b<>bk).
  { intros b HV;repeat split;allocated_distinct. }
  assert (FAlloc : lframe (fun _ _=>True) m mi) by allocated_frame.
  pose proof (field_at_lframe m mi bp 0 _ _ X FAlloc ltac:(intros;exact I)) as XI.
  pose proof (field_at_lframe m mi bp 40 _ _ Y FAlloc ltac:(intros;exact I)) as YI.
  pose proof (field_at_lframe m mi bp 80 _ _ Z FAlloc ltac:(intros;exact I)) as ZI.
  pose proof (field_at_lframe m mi ba 0 _ _ U FAlloc ltac:(intros;exact I)) as UI.
  pose proof (field_at_lframe m mi ba 40 _ _ V FAlloc ltac:(intros;exact I)) as VI.
  pose proof (curve_keep_free _ m mi bp 128 ltac:(lia) PF FAlloc ltac:(intros;exact I)) as PFI.
  pose proof (curve_keep_free _ m mi ba 88 ltac:(lia) AF FAlloc ltac:(intros;exact I)) as AFI.
  pose proof (curve_keep_free _ m mi br 40 ltac:(lia) RF FAlloc ltac:(intros;exact I)) as RFI.
  assert (FlagAI : Mem.load Mint32 mi bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FAlloc Mint32 bp 120 HVP ltac:(intros;exact I));exact FlagA. }
  assert (FlagBI : Mem.load Mint32 mi ba 80=Some (Vint Int.zero)).
  { rewrite (proj1 FAlloc Mint32 ba 80 HVA ltac:(intros;exact I));exact FlagB. }
  assert (FZI : Mem.range_perm mi bz 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
  assert (FUI : Mem.range_perm mi bu 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
  assert (FVI : Mem.range_perm mi bv 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
  assert (FSI : Mem.range_perm mi bs 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
  assert (FTI : Mem.range_perm mi bt 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
  assert (FHI : Mem.range_perm mi bh 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
  assert (FII : Mem.range_perm mi bi 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
  assert (F2I : Mem.range_perm mi b2 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
  assert (F3I : Mem.range_perm mi b3 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
  assert (FKI : Mem.range_perm mi bk 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
  pose proof SepAll as SepAll0;separate_ratio_blocks SepAll0.
  assert (SepB : NoDup [br;bh;bi;bp;ba;bu;bv;bs;bt;bz]).
  { repeat constructor;cbn [In];intuition congruence. }
  destruct (exec_mixed_equal_ratio_body (mixed_helper_env bz bu bv bs bt bh bi b2 b3 bk)
    (mixed_ratio_entry_temps bp ba br) mi bp ba bu bv bs bt bz bh bi br x y z u v
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl SepB FlagAI FlagBI BX BY BZ BU BV H0 I0
    XI YI ZI UI VI PFI AFI FUI FVI FSI FTI FZI FHI FII RFI)
    as (mo & CB & XO & YO & ZO & FlagO & PFO & AFO & UFO & VFO & SFO & TFO & ZFO & HFO & IFO &
      BXO & BYO & BZO & RY & RFO & FB).
  assert (F2O : Mem.range_perm mo b2 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F2I|exact FB|];intros pos.
    unfold mixed_finite_return_frame;repeat split;congruence. }
  assert (F3O : Mem.range_perm mo b3 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F3I|exact FB|];intros pos.
    unfold mixed_finite_return_frame;repeat split;congruence. }
  assert (FKO : Mem.range_perm mo bk 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FKI|exact FB|];intros pos.
    unfold mixed_finite_return_frame;repeat split;congruence. }
  destruct (free_list_exists [(bt,0,40);(bs,0,40);(bi,0,40);(bv,0,40);(bu,0,40);(b2,0,40);(bh,0,40);(b3,0,40);(bk,0,40);(bz,0,40)] mo)
    as (mf & Free & Unchanged).
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi Hin;cbn [In] in Hin.
    repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin] end;
      try contradiction;inversion Hin;subst b lo hi;assumption.
  - assert (FFree : lframe (fun b _=>
        b<>bz /\ b<>bu /\ b<>bv /\ b<>bs /\ b<>bt /\ b<>bh /\ b<>bi /\ b<>b2 /\ b<>b3 /\ b<>bk) mo mf).
    { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
      intros b pos (NZ & NU & NV & NS & NT & NH & NI & N2 & N3 & NK) HV;cbn;intuition congruence. }
    pose proof (field_at_lframe mo mf bp 0 _ _ XO FFree ltac:(intros;exact (Old bp HVP))) as XF.
    pose proof (field_at_lframe mo mf bp 40 _ _ YO FFree ltac:(intros;exact (Old bp HVP))) as YF.
    pose proof (field_at_lframe mo mf bp 80 _ _ ZO FFree ltac:(intros;exact (Old bp HVP))) as ZF.
    pose proof (field_at_lframe mo mf br 0 _ _ RY FFree ltac:(intros;exact (Old br HVR))) as RYF.
    pose proof (curve_keep_free _ mo mf bp 128 ltac:(lia) PFO FFree ltac:(intros;exact (Old bp HVP))) as PFF.
    pose proof (curve_keep_free _ mo mf ba 88 ltac:(lia) AFO FFree ltac:(intros;exact (Old ba HVA))) as AFF.
    pose proof (curve_keep_free _ mo mf br 40 ltac:(lia) RFO FFree ltac:(intros;exact (Old br HVR))) as RFF.
    assert (FlagF : Mem.load Mint32 mf bp 120=Some (Vint (double_var_zflag y z))).
    { rewrite (proj1 FFree Mint32 bp 120);[exact FlagO| |intros;exact (Old bp HVP)].
      eapply Mem.perm_valid_block;apply (PFO 0);lia. }
    assert (FrameOld : lframe (fun b _=>Mem.valid_block m b /\ b<>bp /\ b<>ba /\ b<>br) m mf).
    { eapply lframe_trans.
      - eapply lframe_implies;[exact FAlloc|];intros;exact I.
      - eapply lframe_trans.
        + eapply lframe_implies;[exact FB|];intros b pos (HV & NP & NA & NR) HVI.
          destruct (Old b HV) as (NZ & NU & NV & NS & NT & NH & NI & N2 & N3 & NK).
          unfold mixed_finite_return_frame;repeat split;assumption.
        + eapply lframe_implies;[exact FFree|];intros b pos (HV & NP & NA & NR) HVO;exact (Old b HV). }
    assert (Frame : lframe (fun b _=>b<>bp /\ b<>ba /\ b<>br) m mf).
    { eapply lframe_implies;[exact FrameOld|];intros b pos HP HV;split;assumption. }
    exists mf;split.
    + eapply eval_funcall_internal with (e:=mixed_helper_env bz bu bv bs bt bh bi b2 b3 bk)
        (le1:=mixed_ratio_entry_temps bp ba br)
        (le2:=PTree.set _t'1 (Vint Int.one) (PTree.set _t'2 (Vint Int.one)
          (mixed_preparation_temps (mixed_ratio_entry_temps bp ba br))))
        (m1:=mi) (m2:=mo) (out:=Out_return None).
      * eapply mixed_ratio_function_entry;eassumption.
      * exact CB.
      * reflexivity.
      * rewrite mixed_function_blocks;exact Free.
    + do 11 (split;[assumption|]);exact Frame.
Qed.
