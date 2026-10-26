(** Whole original in-place mixed-addition helper on loose coordinates,
    with an indexed ratio output, all ten allocations, every branch and all
    ten frees. The affine source is retained for the next table iteration. *)
From Coq Require Import ZArith List Lia Sorting.Permutation.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_mixed_function
 C.jet_secp_mixed_body C.jet_secp_mixed_finite_body C.jet_secp_mixed_finite_return
 C.jet_secp_mixed_preparation C.jet_secp_mixed_preparation_loose C.jet_secp_mixed_finite_loose
 C.jet_secp_mixed_body_loose C.jet_secp_mixed_body_ratio_slice C.jet_secp_mixed_finite_ratio_slice
 C.jet_secp_mixed_function_loose C.jet_secp_slice_permissions C.jet_clight_internal_permissions
 C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition mixed_slice_entry_temps bp ba br base := PTree.set _rzr (Vptr br (Ptrofs.repr base)) (mixed_entry_temps bp ba).
Lemma mixed_slice_function_entry m m1 m2 m3 m4 m5 m6 m7 m8 m9 mi bp ba br base bz bu bv bs bt bh bi b2 b3 bk :
 Mem.alloc m 0 40=(m1,bz) -> Mem.alloc m1 0 40=(m2,bu) -> Mem.alloc m2 0 40=(m3,bv) ->
 Mem.alloc m3 0 40=(m4,bs) -> Mem.alloc m4 0 40=(m5,bt) -> Mem.alloc m5 0 40=(m6,bh) ->
 Mem.alloc m6 0 40=(m7,bi) -> Mem.alloc m7 0 40=(m8,b2) -> Mem.alloc m8 0 40=(m9,b3) -> Mem.alloc m9 0 40=(mi,bk) ->
 function_entry2 secp_ge f_secp256k1_gej_add_ge_var
 [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br (Ptrofs.repr base)] m
 (mixed_helper_env bz bu bv bs bt bh bi b2 b3 bk) (mixed_slice_entry_temps bp ba br base) mi.
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

Theorem eval_mixed_ratio_slice_mode (loose:bool) x y z u v flag m bp ba br base size :
  0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned ->
  NoDup [bp;ba;br] ->
  mixed_x_body_bound loose x ->
  square_input_bounds y ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
  Mem.load Mint32 m bp 120=Some (Vint flag) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m br 0 size Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_ge_var)
    [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br (Ptrofs.repr base)] E0 mf Vundef /\
  fe_at mf bp 0 (words5 (mixed_mode_body_x_words loose flag x y z u v)) /\
  fe_at mf bp 40 (words5 (mixed_mode_body_y_words loose flag x y z u v)) /\
  fe_at mf bp 80 (words5 (mixed_mode_body_z_words loose flag x y z u v)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_mode_body_flag loose flag x y z u v)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  square_input_bounds (mixed_mode_body_x_words loose flag x y z u v) /\
  square_input_bounds (mixed_mode_body_y_words loose flag x y z u v) /\
  square_input_bounds (mixed_mode_body_z_words loose flag x y z u v) /\
  fe_at mf br base (words5 (mixed_mode_slice_ratio_words loose flag x y z u v)) /\ Mem.range_perm mf br 0 size Cur Freeable /\
  fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\
  Mem.load Mint32 mf ba 80=Some (Vint Int.zero) /\
  square_input_bounds (mixed_mode_slice_ratio_words loose flag x y z u v) /\
  keeps_permissions m mf /\ lframe (fun b pos=>b<>bp /\ b<>ba /\ (b<>br \/ pos<base \/ base+40<=pos)) m mf /\
  readonly_preserved m mf.
Proof.
  intros Base Align Fit Max SepIn BX BY BZ BU BV FlagA FlagB X Y Z U V PF AF RF.
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
  assert (SepAll : NoDup [bp;ba;bu;bv;bs;bt;bz;bh;bi;b2;b3;bk;br]).
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
  pose proof (curve_keep_free _ m mi br size ltac:(clear -Base Fit;lia) RF FAlloc ltac:(intros;exact I)) as RFI.
  assert (FlagAI : Mem.load Mint32 mi bp 120=Some (Vint flag)).
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
  destruct (exec_mixed_body_ratio_slice loose (mixed_helper_env bz bu bv bs bt bh bi b2 b3 bk)
    (mixed_slice_entry_temps bp ba br base) mi bp ba bu bv bs bt bz bh bi b2 b3 bk br base size x y z u v flag Base Align Fit Max
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl SepAll FlagAI FlagBI BX BY BZ BU BV
    XI YI ZI UI VI PFI AFI FUI FVI FSI FTI FZI FHI FII F2I F3I FKI RFI)
    as (mo & CB & XO & YO & ZO & FlagO & URead & VRead & BFlag & RY & PFO & AFO & UFO & VFO & SFO & TFO & ZFO & HFO & IFO & F2O & F3O & FKO &
      RFO & BXO & BYO & BZO & BRY & FB).
  pose proof SepAll as SepAll0;separate_ratio_blocks SepAll0.
  destruct (free_list_exists [(bt,0,40);(bs,0,40);(bi,0,40);(bv,0,40);(bu,0,40);(b2,0,40);(bh,0,40);(b3,0,40);(bk,0,40);(bz,0,40)] mo)
    as (mf & Free & Unchanged).
  - clear -SepAll; cbn.
    assert (NDFree : NoDup [bt;bs;bi;bv;bu;b2;bh;b3;bk;bz]).
    { pose proof (@NoDup_remove_1 block
        [bp;ba;bu;bv;bs;bt;bz;bh;bi;b2;b3;bk] [] br SepAll) as WithoutRatio.
      pose proof (@NoDup_app_remove_l block [bp;ba]
        [bu;bv;bs;bt;bz;bh;bi;b2;b3;bk] WithoutRatio) as Locals.
      eapply (@Permutation_NoDup block
        [bu;bv;bs;bt;bz;bh;bi;b2;b3;bk]
        [bt;bs;bi;bv;bu;b2;bh;b3;bk;bz]).
      - apply NoDup_Permutation_bis; [exact Locals|cbn;lia|].
        intros value HIn; cbn in HIn |- *; tauto.
      - exact Locals. }
    clear -NDFree.
    assert (Convert : forall xs : list block, NoDup xs -> list_norepet xs).
    { intros xs ND; induction ND; constructor; assumption. }
    exact (Convert _ NDFree).
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
    pose proof (field_at_lframe mo mf br base _ _ RY FFree ltac:(intros;exact (Old br HVR))) as RYF.
    pose proof (curve_keep_free _ mo mf bp 128 ltac:(lia) PFO FFree ltac:(intros;exact (Old bp HVP))) as PFF.
    pose proof (curve_keep_free _ mo mf ba 88 ltac:(lia) AFO FFree ltac:(intros;exact (Old ba HVA))) as AFF.
    pose proof (curve_keep_free _ mo mf br size ltac:(clear -Base Fit;lia) RFO FFree ltac:(intros;exact (Old br HVR))) as RFF.
    assert (FlagF : Mem.load Mint32 mf bp 120=Some (Vint (mixed_mode_body_flag loose flag x y z u v))).
    { rewrite (proj1 FFree Mint32 bp 120);[exact FlagO| |intros;exact (Old bp HVP)].
      eapply Mem.perm_valid_block;apply (PFO 0);lia. }
    assert (FrameOld : lframe (fun b pos=>Mem.valid_block m b /\ b<>bp /\ b<>ba /\ (b<>br \/ pos<base \/ base+40<=pos)) m mf).
    { eapply lframe_trans.
      - eapply lframe_implies;[exact FAlloc|];intros;exact I.
      - eapply lframe_trans.
        + eapply lframe_implies;[exact FB|];intros b pos (HV & NP & NA & NR) HVI.
          destruct (Old b HV) as (NZ & NU & NV & NS & NT & NH & NI & N2 & N3 & NK).
          unfold mixed_finite_slice_frame,mixed_finite_body_frame,mixed_finite_return_frame;repeat split;assumption.
        + eapply lframe_implies;[exact FFree|];intros b pos (HV & NP & NA & NR) HVO;exact (Old b HV). }
    assert (Frame : lframe (fun b pos=>b<>bp /\ b<>ba /\ (b<>br \/ pos<base \/ base+40<=pos)) m mf).
    { eapply lframe_implies;[exact FrameOld|];intros b pos HP HV;split;assumption. }
    assert (UReadF:fe_at mf ba 0 (words5 u)) by
      (eapply field_at_lframe;[exact URead|exact FFree|];intros;exact (Old ba HVA)).
    assert (VReadF:fe_at mf ba 40 (words5 v)) by
      (eapply field_at_lframe;[exact VRead|exact FFree|];intros;exact (Old ba HVA)).
    assert (BFlagF:Mem.load Mint32 mf ba 80=Some (Vint Int.zero)).
    { rewrite (proj1 FFree Mint32 ba 80);[exact BFlag| |intros;exact (Old ba HVA)].
      eapply Mem.perm_valid_block;apply (AFO 0);lia. }
    assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_ge_var)
      [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br (Ptrofs.repr base)] E0 mf Vundef).
    { eapply eval_funcall_internal with (e:=mixed_helper_env bz bu bv bs bt bh bi b2 b3 bk)
        (le1:=mixed_slice_entry_temps bp ba br base) (le2:=mixed_mode_body_temps loose (mixed_slice_entry_temps bp ba br base) flag x y z u v)
        (m1:=mi) (m2:=mo) (out:=mixed_body_out flag (mixed_x_words loose x) z u).
      * eapply mixed_slice_function_entry;eassumption.
      * exact CB.
      * apply mixed_function_result.
      * rewrite mixed_function_blocks;exact Free.
    }
    assert (Keep:keeps_permissions m mf) by
      (eapply (secp_internal_keeps_permissions f_secp256k1_gej_add_ge_var);
        [exact mixed_function_closed|reflexivity|exact Call]).
    assert (Readonly:readonly_preserved m mf) by (eapply mixed_function_readonly;exact Call).
    exists mf;repeat (first [assumption|split]).
Qed.
