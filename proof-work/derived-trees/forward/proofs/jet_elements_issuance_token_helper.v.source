(** [issuanceTokenAmt] as a function: the local is allocated, the tag bit is
    written, the present branch runs or padding is skipped, and the local is
    freed.  The result is a plain [write_effect], as for the other helpers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_uint32_array_init C.jet_application_sep.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval C.jet_elements_effects.
Require Import C.jet_output_layout_step C.jet_wide C.jet_wide_spec C.jet_elements_steps C.jet_elements_env_load C.jet_elements_write32s_layout C.jet_elements_hash_write C.jet_elements_call.
Require C.jets.
Require Import C.jet_elements_transport C.jet_elements_indexed_exec C.jet_elements_hash_helpers C.jet_elements_indexed_ptr C.jet_elements_asset_helper C.jet_elements_amt_helper.
Require Import C.jet_elements_indexed_scalar C.jet_elements_issuance_helper C.jet_elements_effects_local.
Require Import JetStartupReview.jet_clight_forward JetForward.jet_elements_issuance_token_then.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.





Theorem eval_elements_issuanceTokenAmt_layout m bi ibase bf base bw edge cursor ty xs v pfx :
  length xs = 8%nat -> 0 <= ibase -> ibase + 280 <= Ptrofs.max_unsigned ->
  out_sep bf base bw edge cursor 259 bi ibase (ibase + 280) ->
  Mem.load Mint32 m bi (ibase + 272) = Some (Vint ty) ->
  (Int.eq (Int.repr 1) ty = true ->
     Mem.load Mint32 m bi (ibase + 32 + 32) = Some (Vint pfx) /\
     (Int.eq (Int.repr 1) pfx = true -> Mem.load Mint64 m bi (ibase + 32) = Some (Vlong v)) /\
     (Int.eq (Int.repr 1) pfx = false -> uint32_array_at m bi (ibase + 32) xs)) ->
  write_frame_at m bf base bw edge cursor 259 ->
  exists mf,
    Clight2.eval_funcall elements_ge m (Internal f_issuanceTokenAmt)
      [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr ibase)] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor 259 (token_cells ty pfx xs v).
Proof.
  intros HL H0 HM HSep HT HNew HF.
  pose proof HF as [_ [_ [_ [HCur [_ [PD _]]]]]].
  assert (Vf : Mem.valid_block m bf).
  { eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies; [exact PD|constructor]. }
  assert (Vw : Mem.valid_block m bw).
  { destruct (write_frame_at_head m bf base bw edge cursor 259 ltac:(lia) HF) as (_ & _ & PW & _).
    eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies; [exact PW|constructor]. }
  assert (Vi : Mem.valid_block m bi).
  { eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies;
      [exact (Mem.load_valid_access _ _ _ _ _ HT)|constructor]. }
  destruct (Mem.alloc m 0 40) as [m1 bc] eqn:HA.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HA) as Hfresh.
  assert (Ncf : bc <> bf) by (intro; subst; contradiction).
  assert (Ncw : bc <> bw) by (intro; subst; contradiction).
  assert (Nci : bc <> bi) by (intro; subst; contradiction).
  assert (HL1 : forall chunk b ofs v', Mem.load chunk m b ofs = Some v' -> Mem.load chunk m1 b ofs = Some v').
  { intros chunk b ofs v' Hl. eapply Mem.load_alloc_other; eauto. }
  assert (HP1 : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm m1 b ofs kind p).
  { intros b ofs kind p H. eapply Mem.perm_alloc_1; eauto. }
  assert (HF1 : write_frame_at m1 bf base bw edge cursor 259).
  { eapply write_frame_at_preserved; [|exact HP1|exact HF]. intros chunk b ofs v' _ Hl. exact (HL1 _ _ _ _ Hl). }
  set (b0 := negb (Int.eq (Int.repr 0) ty)).
  assert (HF1a : write_frame_at m1 bf base bw edge cursor 1).
  { eapply write_frame_at_shorter; [|exact HF1]. lia. }
  destruct (elements_writeBit_step m1 bf base bw edge cursor b0 HF1a) as (mb & HCallB & E1).
  assert (HFb : write_frame_at mb bf base bw edge (cursor - 1) 258).
  { eapply write_frame_at_after_effect with (cells := [Some b0]); [reflexivity|lia|exact HF1|exact E1]. }
  assert (HLoadB : forall chunk o, ibase <= o -> o + size_chunk chunk <= ibase + 280 ->
    Mem.load chunk mb bi o = Mem.load chunk m1 bi o).
  { intros chunk o Hlo Hhi.
    eapply write_effect_env_load with (bf := bf) (base := base) (bw := bw) (edge := edge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 259) (n := 1) (cells := [Some b0])
      (lo := ibase) (hi := ibase + 280); [lia|lia|lia|lia|exact E1|exact HSep|exact Hlo|exact Hhi]. }
  assert (HKeep : forall chunk o v', ibase <= o -> o + size_chunk chunk <= ibase + 280 ->
    Mem.load chunk m bi o = Some v' -> Mem.load chunk mb bi o = Some v').
  { intros chunk o v' Hlo Hhi Hl. rewrite (HLoadB chunk o Hlo Hhi). exact (HL1 _ _ _ _ Hl). }
  set (le0 := PTree.set _issuance (Vptr bi (Ptrofs.repr ibase))
    (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps (fn_temps f_issuanceTokenAmt)))).
  set (le1 := PTree.set _t'4 (Vint ty) le0).
  set (le2 := PTree.set _t'2 (Vint (conf_bit_int b0)) le1).
  assert (HD2 : le2!_dst = Some (Vptr bf (Ptrofs.repr base))).
  { unfold le2, le1, le0. gso1. gso1. gso1. apply PTree.gss. }
  assert (HI2 : le2!_issuance = Some (Vptr bi (Ptrofs.repr ibase))).
  { unfold le2, le1, le0. gso1. gso1. apply PTree.gss. }
  assert (X1 : write_effect_x bc m1 mb bf base bw edge cursor 1 [Some b0])
    by exact (write_effect_to_x bc _ _ _ _ _ _ _ _ _ E1).
  assert (HTail : exists le' me,
    Clight2.exec_stmt elements_ge (token_env bc) le2 mb
      (if b0 then token_then else elements_skip_stmt 258) E0 le' me Out_normal /\
    write_effect_x bc m1 me bf base bw edge cursor (1 + 258) (token_cells ty pfx xs v)).
  { unfold token_cells, issuance_tagged_cells. fold b0. destruct b0 eqn:Hb0.
    - assert (HPc : Mem.range_perm mb bc 0 40 Cur Writable).
      { intros o Ho. destruct E1 as (_ & _ & _ & _ & Pm & _). apply Pm.
        eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto|constructor]. }
      assert (HSepB : out_sep bf base bw edge (cursor - 1) 258 bi ibase (ibase + 280)).
      { eapply out_sep_sub with (cursor := cursor) (count := 259); [lia|lia|lia|lia|exact HSep]. }
      assert (HNewB : Int.eq (Int.repr 1) ty = true ->
        Mem.load Mint32 mb bi (ibase + 32 + 32) = Some (Vint pfx) /\
        (Int.eq (Int.repr 1) pfx = true -> Mem.load Mint64 mb bi (ibase + 32) = Some (Vlong v)) /\
        (Int.eq (Int.repr 1) pfx = false -> uint32_array_at mb bi (ibase + 32) xs)).
      { intros Hn. destruct (HNew Hn) as (Hp & Hv & Ha). split; [|split].
        - apply HKeep; [lia|change (size_chunk Mint32) with 4; lia|exact Hp].
        - intros Hx. apply HKeep; [lia|change (size_chunk Mint64) with 8; lia|exact (Hv Hx)].
        - intros Hx i w Hi.
          assert (Hi8 : (i < 8)%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hi; discriminate).
          apply HKeep; [lia|change (size_chunk Mint32) with 4; lia|exact (Ha Hx i w Hi)]. }
      destruct (exec_token_then le2 mb bc bi ibase bf base bw edge (cursor - 1) ty xs v pfx
        HD2 HI2 HL H0 HM Ncf Ncw Nci HPc HSepB
        (HKeep Mint32 (ibase + 272) _ ltac:(lia) ltac:(change (size_chunk Mint32) with 4; lia) HT)
        HNewB HFb) as (le' & ms & me & HEx & HLs & HPs & HVs & E2).
      exists le', me. split; [exact HEx|].
      pose proof (write_effect_x_step bc m1 mb ms bf base bw edge cursor 1 [Some true]
        Ncf Ncw HLs HPs HVs X1) as X1'.
      exact (write_effect_x_seq bc m1 ms me bf base bw edge cursor 1 258 [Some true] _
        eq_refl ltac:(lia) HF1 X1' E2).
    - destruct (elements_skipBits_step mb bf base bw edge (cursor - 1) 258%nat HFb) as (me & HCallS & E2).
      exists le2, me. split.
      + unfold elements_skip_stmt.
        assert (Hargs : eval_exprlist elements_ge (token_env bc) le2 mb
          [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 258) tint]
          (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
          [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (Z.of_nat 258))]).
        { eapply eval_Econs; [apply eval_Etempvar; exact HD2|reflexivity|].
          eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
          apply elements_cast_const'; lia. }
        exact (exec_elements_helper_call (token_env bc) le2 mb None _skipBits jets.f_skipBits
          _ _ _ _ _ _ me ltac:(unfold elements_core_helpers; simpl; tauto) ltac:(reflexivity) Hargs
          ltac:(reflexivity) HCallS).
      + exact (write_effect_x_seq bc m1 mb me bf base bw edge cursor 1 258 [Some false] _
          eq_refl ltac:(lia) HF1 X1 E2). }
  destruct HTail as (le' & me & HT' & X).
  assert (HBody : Clight2.exec_stmt elements_ge (token_env bc) le0 m1 (fn_body f_issuanceTokenAmt)
    E0 le' me Out_normal).
  { unfold f_issuanceTokenAmt; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le2).
    - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1).
      + apply exec_set.
        eapply eval_elements_field_value with (sid := _assetIssuance) (delta := 272) (chunk := Mint32).
        * reflexivity.
        * exact elements_assetIssuance_type.
        * reflexivity.
        * apply eval_elements_deref_struct. unfold le0. apply PTree.gss.
        * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact (HL1 _ _ _ _ HT)].
      + change le2 with (set_opttemp (Some _t'2) (Vint (conf_bit_int b0)) le1).
        eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit)
          (vargs := [Vptr bf (Ptrofs.repr base); Vint (conf_bit_int b0)]) (vres := Vint (conf_bit_int b0)).
        * unfold elements_core_helpers. simpl. tauto.
        * reflexivity.
        * eapply eval_Econs.
          -- apply eval_Etempvar. unfold le1, le0. gso1. gso1. apply PTree.gss.
          -- reflexivity.
          -- eapply eval_Econs with (v1 := Val.of_bool b0).
             ++ eapply eval_Ebinop with (v1 := Vint (Int.repr 0)) (v2 := Vint ty).
                ** apply eval_Econst_int.
                ** apply eval_Etempvar. unfold le1. apply PTree.gss.
                ** apply elements_ne_cmp.
             ++ apply elements_bool_cast.
             ++ apply eval_Enil.
        * reflexivity.
        * exact HCallB.
    - eapply exec_Sifthenelse with (v1 := Vint (conf_bit_int b0)) (b := b0).
      + apply eval_Etempvar. unfold le2. apply PTree.gss.
      + destruct b0; reflexivity.
      + destruct b0; exact HT'. }
  assert (V1c : Mem.valid_block m1 bc) by exact (Mem.valid_new_block _ _ _ _ _ HA).
  destruct (proj1 (clight_exec_forward elements_ge) _ _ _ _ _ _ _ _ HBody bc V1c) as [_ HMax].
  assert (HPerm : forall ofs kind p, Mem.perm me bc ofs kind p -> 0 <= ofs < 40).
  { intros ofs kind p H.
    assert (HM' : Mem.perm me bc ofs Max p) by (destruct kind; [exact H|apply Mem.perm_cur_max; exact H]).
    exact (Mem.perm_alloc_3 _ _ _ _ _ HA _ _ _ (HMax _ _ HM')). }
  assert (HFreeable : Mem.range_perm me bc 0 40 Cur Freeable).
  { intros o Ho. destruct X as (_ & _ & _ & _ & Pm & _). apply Pm. eapply Mem.perm_alloc_2; eauto. }
  destruct (Mem.range_perm_free me bc 0 40 HFreeable) as [mf HFree].
  exists mf. split.
  - eapply eval_funcall_internal with (e := token_env bc) (le1 := le0) (le2 := le')
      (m1 := m1) (m2 := me) (out := Out_normal).
    + constructor.
      * repeat constructor; simpl; tauto.
      * change (list_norepet [_dst; _issuance]). unfold _dst, _issuance.
        repeat constructor; simpl; intuition discriminate.
      * intros i j HI HJ Hij. cbn in HI, HJ.
        repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
          first [contradiction | vm_compute in Hij; discriminate | congruence].
      * econstructor; [rewrite elements_sizeof_confAmount; exact HA|constructor].
      * reflexivity.
    + exact HBody.
    + reflexivity.
    + unfold blocks_of_env, token_env.
      change (PTree.elements (PTree.set ___compound (bc, Tstruct _confAmount noattr) empty_env))
        with [(___compound, (bc, Tstruct _confAmount noattr))].
      cbn [map block_of_binding]. rewrite elements_sizeof_confAmount.
      cbn [Mem.free_list]. rewrite HFree. reflexivity.
  - change 259 with (1 + 258).
    exact (write_effect_x_close bc 0 40 m m1 me mf bf base bw edge cursor (1 + 258) _ HA Ncf Ncw X HPerm HFree).
Qed.
