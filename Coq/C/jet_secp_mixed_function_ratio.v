(** Complete original non-NULL-ratio mixed-addition helper: the incoming-
    infinity branch and every finite H/I branch, with all ten allocations and
    frees. Unlike the equal-point-only ratio function, nothing is excluded. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
  C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_mixed_function
  C.jet_secp_mixed_body C.jet_secp_mixed_finite_body C.jet_secp_mixed_finite_return
  C.jet_secp_mixed_preparation C.jet_secp_mixed_ratio_function C.jet_secp_mixed_ratio_branches
  C.jet_secp_mixed_finite_ratio C.jet_secp_mixed_infinite_literal C.jet_secp_point_set_bit.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_body_ratio_words flag x y z u v : nat -> int64 :=
  if Int.eq flag Int.zero then mixed_finite_ratio_words x y z u v else zero_words.

Local Ltac separate_body_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_body_owned HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.

Theorem exec_mixed_body_ratio e le m bp ba bu bv bs bt bz bh bi b2 b3 bk br x y z u v flag :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vptr br Ptrofs.zero) ->
  e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
  e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
  e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
  e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) -> e!_t=Some (bk,curve_fe_type) ->
  e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_gej_set_ge=None ->
  e!_secp256k1_fe_set_int=None -> e!_secp256k1_fe_clear=None ->
  NoDup [bp;ba;bu;bv;bs;bt;bz;bh;bi;b2;b3;bk;br] ->
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
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> Mem.range_perm m bk 0 40 Cur Freeable ->
  Mem.range_perm m br 0 40 Cur Freeable -> exists mf,
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
  fe_at mf br 0 (words5 (mixed_body_ratio_words flag x y z u v)) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun bx pos=>mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk bx pos /\ bx<>br) m mf.
Proof.
  intros HA HB HR HN EU EV ES ET EZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF EG ESI ECL Sep FlagA FlagB BX BY BZ BU BV
    X Y Z U V PF AF UF VF SF TF ZF HF IF F2 F3 FK RF.
  unfold mixed_body_temps,mixed_body_out,mixed_body_x_words,mixed_body_y_words,mixed_body_z_words,
    mixed_body_flag,mixed_body_ratio_words.
  destruct (Int.eq_dec flag Int.zero) as [->|HFlag].
  - rewrite Int.eq_true.
    exact (exec_mixed_finite_body_ratio e le m bp ba bu bv bs bt bz bh bi b2 b3 bk br x y z u v
      HA HB HR HN EU EV ES ET EZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF ESI Sep FlagA FlagB BX BY BZ BU BV
      X Y Z U V PF AF UF VF SF TF ZF HF IF F2 F3 FK RF).
  - rewrite Int.eq_false by exact HFlag;pose proof Sep as Sep0;separate_body_blocks Sep0.
    destruct (mixed_infinite_body_ratio e le m bp ba br u v flag HA HR HB HN EG ECL
      ltac:(congruence) ltac:(congruence) ltac:(congruence) PF RF FlagA HFlag U V FlagB)
      as (mf & CB & XO & YO & ZO & FlagO & PFO & RO & RFO & FB).
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
    assert (Frame : lframe (fun bx pos=>mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk bx pos /\ bx<>br) m mf).
    { eapply lframe_implies;[exact FB|];
        intros bx pos (((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & N2 & N3 & NK) & NR) HV;exact (conj NP NR). }
    exists mf;repeat (first [assumption|exact mixed_one_bounds|split]).
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

Theorem eval_mixed_ratio_function x y z u v flag m bp ba br :
  NoDup [bp;ba;br] ->
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  fe_limbs_ok (Int64.unsigned (y 0%nat)) (Int64.unsigned (y 1%nat))
    (Int64.unsigned (y 2%nat)) (Int64.unsigned (y 3%nat)) (Int64.unsigned (y 4%nat)) ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
  Mem.load Mint32 m bp 120=Some (Vint flag) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m br 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_ge_var)
    [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bp 0 (words5 (mixed_body_x_words flag x y z u v)) /\
  fe_at mf bp 40 (words5 (mixed_body_y_words flag x y z u v)) /\
  fe_at mf bp 80 (words5 (mixed_body_z_words flag x y z u v)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (mixed_body_flag flag x y z u v)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  square_input_bounds (mixed_body_x_words flag x y z u v) /\
  square_input_bounds (mixed_body_y_words flag x y z u v) /\
  square_input_bounds (mixed_body_z_words flag x y z u v) /\
  fe_at mf br 0 (words5 (mixed_body_ratio_words flag x y z u v)) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun b _=>b<>bp /\ b<>ba /\ b<>br) m mf.
Proof.
  intros SepIn BX BY BZ BU BV FlagA FlagB X Y Z U V PF AF RF.
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
  pose proof (curve_keep_free _ m mi br 40 ltac:(lia) RF FAlloc ltac:(intros;exact I)) as RFI.
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
  destruct (exec_mixed_body_ratio (mixed_helper_env bz bu bv bs bt bh bi b2 b3 bk)
    (mixed_ratio_entry_temps bp ba br) mi bp ba bu bv bs bt bz bh bi b2 b3 bk br x y z u v flag
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl SepAll FlagAI FlagBI BX BY BZ BU BV
    XI YI ZI UI VI PFI AFI FUI FVI FSI FTI FZI FHI FII F2I F3I FKI RFI)
    as (mo & CB & XO & YO & ZO & FlagO & PFO & AFO & UFO & VFO & SFO & TFO & ZFO & HFO & IFO & F2O & F3O & FKO &
      BXO & BYO & BZO & RY & RFO & FB).
  pose proof SepAll as SepAll0;separate_ratio_blocks SepAll0.
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
    assert (FlagF : Mem.load Mint32 mf bp 120=Some (Vint (mixed_body_flag flag x y z u v))).
    { rewrite (proj1 FFree Mint32 bp 120);[exact FlagO| |intros;exact (Old bp HVP)].
      eapply Mem.perm_valid_block;apply (PFO 0);lia. }
    assert (FrameOld : lframe (fun b _=>Mem.valid_block m b /\ b<>bp /\ b<>ba /\ b<>br) m mf).
    { eapply lframe_trans.
      - eapply lframe_implies;[exact FAlloc|];intros;exact I.
      - eapply lframe_trans.
        + eapply lframe_implies;[exact FB|];intros b pos (HV & NP & NA & NR) HVI.
          destruct (Old b HV) as (NZ & NU & NV & NS & NT & NH & NI & N2 & N3 & NK).
          unfold mixed_finite_body_frame,mixed_finite_return_frame;repeat split;assumption.
        + eapply lframe_implies;[exact FFree|];intros b pos (HV & NP & NA & NR) HVO;exact (Old b HV). }
    assert (Frame : lframe (fun b _=>b<>bp /\ b<>ba /\ b<>br) m mf).
    { eapply lframe_implies;[exact FrameOld|];intros b pos HP HV;split;assumption. }
    exists mf;split.
    + eapply eval_funcall_internal with (e:=mixed_helper_env bz bu bv bs bt bh bi b2 b3 bk)
        (le1:=mixed_ratio_entry_temps bp ba br) (le2:=mixed_body_temps (mixed_ratio_entry_temps bp ba br) flag x y z u v)
        (m1:=mi) (m2:=mo) (out:=mixed_body_out flag x z u).
      * eapply mixed_ratio_function_entry;eassumption.
      * exact CB.
      * apply mixed_function_result.
      * rewrite mixed_function_blocks;exact Free.
    + repeat (first [assumption|split]).
Qed.
