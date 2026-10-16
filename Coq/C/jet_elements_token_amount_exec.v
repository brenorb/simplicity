(** Full static issuanceTokenAmt call, including allocation and free. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Memory Events Globalenvs ClightBigstep.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jets_elements C.jet_elements_linkage C.jet_elements_prim.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_application_sep C.jet_elements_effects C.jet_elements_steps C.jet_elements_call.
Require Import C.jet_elements_field_eval C.jet_elements_version_exec C.jet_elements_hash_helpers.
Require Import C.jet_elements_asset_helper C.jet_elements_amt_helper C.jet_elements_amount_jets.
Require Import C.jet_elements_issuance_helper C.jet_elements_issuance_jets C.jet_elements_issuance_amount_jets.
Require Import C.jet_elements_indexed_ptr C.jet_elements_token_select C.jet_local_alloc_effect.
Require Import C.jet_elements_indexed_scalar.
Require Import C.jet_elements_transport.
Require Import C.jet_elements_indexed_exec.
Require Import C.jet_output_layout_step C.jet_elements_env_load.
Import Values Mem Ctypes ListNotations Clightdefs.
Require C.jets.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition token_issuance_rep m bi ibase (o : option issuance) :=
  Mem.load Mint32 m bi (ibase + 272) = Some (Vint (issuance_tag o)) /\
  forall new, o = Some (inl new) -> amount_rep m bi (ibase + 32) (clearPrf (newIssuanceTokenAmount new)).
Definition token_issuance_tail (o : option issuance) : list Cell :=
  match o with Some i => amount_pcells (token_selected_amount i) | None => repeat None 258 end.
Definition token_issuance_cells (o : option issuance) := [Some (opt_is_some o)] ++ token_issuance_tail o.

Lemma token_issuance_rep_pres m1 m2 bi ibase o :
  token_issuance_rep m1 bi ibase o ->
  (forall chunk ofs v, ibase <= ofs -> ofs + size_chunk chunk <= ibase + 280 ->
    Mem.load chunk m1 bi ofs = Some v -> Mem.load chunk m2 bi ofs = Some v) ->
  token_issuance_rep m2 bi ibase o.
Proof.
  intros [HT HA] HL. split.
  - apply HL; [lia|change (size_chunk Mint32) with 4; lia|exact HT].
  - intros new Hnew. eapply amount_rep_mono; [apply HA; exact Hnew|].
    intros chunk ofs v H0 HM HV. apply HL; [lia|lia|exact HV].
Qed.

Definition token_first_stmt := Ssequence
  (Sset _t'4 (Efield
    (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr))) (Tstruct _assetIssuance noattr)) _type tint))
  (Scall (Some _t'2)
    (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Ebinop One (Econst_int Int.zero tint) (Etempvar _t'4 tint) tint]).
Definition token_helper_env bc := PTree.set ___compound (bc, Tstruct _confAmount noattr) empty_env.
Definition token_helper_temps bf base bi ibase := PTree.set _issuance (Vptr bi (Ptrofs.repr ibase))
  (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps (fn_temps f_issuanceTokenAmt))).
Definition token_first_temps le o := PTree.set _t'2 (Vint (conf_bit_int (opt_is_some o)))
  (PTree.set _t'4 (Vint (issuance_tag o)) le).

Lemma token_helper_shape : fn_body f_issuanceTokenAmt = Ssequence token_first_stmt
  (Sifthenelse (Etempvar _t'2 tbool) token_armed_stmt (elements_skip_stmt 258)).
Proof. reflexivity. Qed.

Lemma token_helper_blocks bc : blocks_of_env elements_ge (token_helper_env bc) = [(bc,0,40)].
Proof. vm_compute; reflexivity. Qed.

Lemma token_helper_entry m ma bc bf base bi ibase :
  Mem.alloc m 0 40 = (ma, bc) ->
  function_entry2 elements_ge f_issuanceTokenAmt
    [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr ibase)] m
    (token_helper_env bc) (token_helper_temps bf base bi ibase) ma.
Proof.
  intro A. constructor.
  - change (list_norepet [___compound]); repeat constructor; cbn; tauto.
  - change (list_norepet [_dst;_issuance]); repeat constructor; cbn; intuition discriminate.
  - intros i j HI HJ Hij. cbn in HI,HJ.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hij; discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bc).
    + change (Mem.alloc m 0 40 = (ma,bc)); exact A.
    + constructor.
  - reflexivity.
Qed.

Lemma exec_token_first e le ma mb bi ibase bf base o :
  e!_writeBit = None -> le!_issuance = Some (Vptr bi (Ptrofs.repr ibase)) ->
  le!_dst = Some (Vptr bf (Ptrofs.repr base)) ->
  0 <= ibase -> ibase + 280 <= Ptrofs.max_unsigned ->
  Mem.load Mint32 ma bi (ibase + 272) = Some (Vint (issuance_tag o)) ->
  Clight2.eval_funcall elements_ge ma (Internal jets.f_writeBit)
    [Vptr bf (Ptrofs.repr base); Vint (conf_bit_int (opt_is_some o))] E0 mb
    (Vint (conf_bit_int (opt_is_some o))) ->
  Clight2.exec_stmt elements_ge e le ma token_first_stmt E0 (token_first_temps le o) mb Out_normal.
Proof.
  intros HG HI HD H0 HM HT HC. unfold token_first_stmt, token_first_temps.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ma)
    (le1 := PTree.set _t'4 (Vint (issuance_tag o)) le).
  - apply exec_set. eapply eval_elements_field_value with (sid := _assetIssuance) (delta := 272) (chunk := Mint32).
    + reflexivity.
    + exact elements_assetIssuance_type.
    + reflexivity.
    + apply eval_elements_deref_struct; exact HI.
    + rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HT].
  - change (PTree.set _t'2 (Vint (conf_bit_int (opt_is_some o)))
      (PTree.set _t'4 (Vint (issuance_tag o)) le)) with
      (set_opttemp (Some _t'2) (Vint (conf_bit_int (opt_is_some o))) (PTree.set _t'4 (Vint (issuance_tag o)) le)).
    eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit).
    + unfold elements_core_helpers; cbn; tauto.
    + exact HG.
    + eapply eval_Econs; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact HD|reflexivity|].
      eapply eval_Econs with (v1 := Val.of_bool (opt_is_some o)).
      * eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vint (issuance_tag o));
          [constructor|apply eval_Etempvar; apply PTree.gss|].
        rewrite <- (issuance_tag_present o). apply elements_ne_cmp.
      * apply elements_bool_cast.
      * constructor.
    + reflexivity.
    + exact HC.
Qed.

Theorem eval_elements_issuanceTokenAmt m bi ibase bf base bw edge cursor o :
  token_issuance_rep m bi ibase o -> 0 <= ibase -> ibase + 280 <= Ptrofs.max_unsigned ->
  out_sep bf base bw edge cursor 259 bi ibase (ibase + 280) ->
  write_frame_at m bf base bw edge cursor 259 ->
  exists mf,
    Clight2.eval_funcall elements_ge m (Internal f_issuanceTokenAmt)
      [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr ibase)] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor 259 (token_issuance_cells o).
Proof.
  intros HR H0 HM HSep HF.
  pose proof HF as [_ [_ [_ [HCur _]]]].
  pose proof HR as [HT HA].
  pose proof HF as [_ [[HDE HDO] _]].
  destruct (write_frame_at_head m bf base bw edge cursor 259 ltac:(lia) HF)
    as (_ & _ & _ & old & HOld).
  destruct (Mem.alloc m 0 40) as [ma bc] eqn:A.
  assert (Fresh : forall b, Mem.valid_block m b -> bc <> b).
  { intros b HV HEq. subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ A HV). }
  assert (Hcd : bc <> bf) by (apply Fresh; eapply load_valid_block; exact HDE).
  assert (Hcw : bc <> bw) by (apply Fresh; eapply load_valid_block; exact HOld).
  assert (HRa : token_issuance_rep ma bi ibase o).
  { eapply token_issuance_rep_pres; [exact HR|]. intros; eapply Mem.load_alloc_other; eauto. }
  assert (HFa : write_frame_at ma bf base bw edge cursor 259).
  { eapply write_frame_at_preserved with (m := m).
    - intros; eapply Mem.load_alloc_other; eauto.
    - intros; eapply Mem.perm_alloc_1; eauto.
    - exact HF. }
  assert (HF1 : write_frame_at ma bf base bw edge cursor 1)
    by (eapply write_frame_at_shorter with (count := 259); [lia|exact HFa]).
  destruct (elements_writeBit_step ma bf base bw edge cursor (opt_is_some o) HF1) as (mb & CB & W1).
  assert (HFb : write_frame_at mb bf base bw edge (cursor - 1) 258).
  { eapply write_frame_at_after_effect with (cells := [Some (opt_is_some o)]) (m := ma);
      [reflexivity|lia|exact HFa|exact W1]. }
  assert (HLoadB : forall chunk ofs, ibase <= ofs -> ofs + size_chunk chunk <= ibase + 280 ->
    Mem.load chunk mb bi ofs = Mem.load chunk ma bi ofs).
  { intros chunk ofs HL HH. eapply write_effect_env_load with
      (bf := bf) (base := base) (bw := bw) (edge := edge) (cursor := cursor)
      (cursor0 := cursor) (count0 := 259) (n := 1) (cells := [Some (opt_is_some o)])
      (lo := ibase) (hi := ibase + 280); eauto; lia. }
  assert (HRb : token_issuance_rep mb bi ibase o).
  { eapply token_issuance_rep_pres; [exact HRa|]. intros; rewrite HLoadB by lia; assumption. }
  pose proof W1 as (_ & _ & _ & _ & PM1 & _).
  assert (PL : Mem.range_perm mb bc 0 40 Cur Writable).
  { intros ofs HO. apply PM1. eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto|constructor]. }
  set (e := token_helper_env bc).
  set (le0 := token_helper_temps bf base bi ibase).
  set (le2 := token_first_temps le0 o).
  assert (HI2 : le2!_issuance = Some (Vptr bi (Ptrofs.repr ibase))).
  { unfold le2, token_first_temps, le0, token_helper_temps.
    rewrite !PTree.gso by discriminate. apply PTree.gss. }
  assert (HD2 : le2!_dst = Some (Vptr bf (Ptrofs.repr base))).
  { unfold le2, token_first_temps, le0, token_helper_temps.
    rewrite !PTree.gso by discriminate. apply PTree.gss. }
  assert (HSepB : out_sep bf base bw edge (cursor - 1) 258 bi ibase (ibase + 280)).
  { eapply out_sep_sub with (cursor := cursor) (count := 259); [lia|lia|lia|lia|exact HSep]. }
  assert (Tail : exists mi me le',
    Clight2.exec_stmt elements_ge e le2 mb
      (if opt_is_some o then token_armed_stmt else elements_skip_stmt 258) E0 le' me Out_normal /\
    write_effect mi me bf base bw edge (cursor - 1) 258 (token_issuance_tail o) /\
    (forall chunk b ofs, b <> bc \/ ofs + size_chunk chunk <= 0 \/ 40 <= ofs ->
      Mem.load chunk mi b ofs = Mem.load chunk mb b ofs) /\
    (forall b ofs kind p, Mem.perm mb b ofs kind p -> Mem.perm mi b ofs kind p) /\
    (forall b, Mem.valid_block mb b -> Mem.valid_block mi b)).
  { destruct o as [i|]; cbn [opt_is_some token_issuance_tail].
    - destruct HRb as [HTb HAb].
      destruct (exec_token_armed e le2 mb i bi ibase bc bf base bw edge (cursor-1)
        ltac:(unfold e, token_helper_env; apply PTree.gss)
        ltac:(unfold e, token_helper_env; rewrite PTree.gso by discriminate; reflexivity)
        HI2 HD2 H0 HM HTb ltac:(intros new Hnew; subst i; apply HAb; reflexivity)
        PL Hcd Hcw HSepB HFb) as (mi & me & EX & WE & HL & PP & VV).
      eexists mi, me, _. split; [exact EX|]. split; [exact WE|].
      split; [exact HL|]. split; assumption.
    - destruct (elements_skipBits_step mb bf base bw edge (cursor-1) 258%nat HFb) as (me & CS & WE).
      exists mb, me, le2. split.
      + unfold elements_skip_stmt. change le2 with (set_opttemp None Vundef le2) at 2.
        eapply exec_elements_helper_call with (id := _skipBits) (f := jets.f_skipBits)
          (vargs := [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr 258)]) (vres := Vundef).
        * unfold elements_core_helpers; cbn; tauto.
        * unfold e, token_helper_env; rewrite PTree.gso by discriminate; reflexivity.
        * eapply eval_Econs; [apply eval_Etempvar; exact HD2|reflexivity|].
          eapply eval_Econs; [constructor|apply elements_cast_const'; lia|constructor].
        * reflexivity.
        * exact CS.
      + split; [exact WE|]. split; [intros; reflexivity|]. split; auto. }
  destruct Tail as (mi & me & le' & ET & W2 & KI & PI & VI).
  assert (PFree : Mem.range_perm me bc 0 40 Cur Freeable).
  { pose proof W2 as (_ & _ & _ & _ & PM2 & _).
    intros ofs HO. apply PM2, PI, PM1. eapply Mem.perm_alloc_2; eauto. }
  destruct (Mem.range_perm_free me bc 0 40 PFree) as [mf F].
  exists mf. split.
  - eapply eval_funcall_internal with (e := e) (le1 := le0) (le2 := le')
      (m1 := ma) (m2 := me) (out := Out_normal).
    + eapply token_helper_entry; exact A.
    + rewrite token_helper_shape. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le2).
      * apply exec_token_first with (bi := bi) (ibase := ibase) (bf := bf) (base := base).
        -- unfold e, token_helper_env; rewrite PTree.gso by discriminate; reflexivity.
        -- unfold le0, token_helper_temps; apply PTree.gss.
        -- unfold le0, token_helper_temps; rewrite PTree.gso by discriminate; apply PTree.gss.
        -- exact H0.
        -- exact HM.
        -- exact (proj1 HRa).
        -- exact CB.
      * eapply exec_Sifthenelse with (v1 := Vint (conf_bit_int (opt_is_some o))) (b := opt_is_some o).
        -- apply eval_Etempvar. unfold le2, token_first_temps; apply PTree.gss.
        -- destruct o; reflexivity.
        -- destruct o; exact ET.
    + reflexivity.
    + change (Mem.free_list me (blocks_of_env elements_ge (token_helper_env bc)) = Some mf).
      rewrite token_helper_blocks. cbn. rewrite F. reflexivity.
  - unfold token_issuance_cells. exact (write_effect_local_alloc m ma mb mi me mf bc 40
      bf base bw edge cursor 258 (opt_is_some o) (token_issuance_tail o)
      ltac:(lia) ltac:(lia) A F HF W1 KI PI VI W2).
Qed.
