(** The static Elements helper [issuanceTokenAmt], whose reissuance branch
    passes a stack-allocated explicit zero to [amt].  The helper allocates
    the local on entry and frees it on return; the effect on the output frame
    is established up to that block ([write_effect_x]) and closed around the
    allocation using the forward-memory property of Clight executions
    (prerequisite [jet_clight_forward], referenced by hash). *)
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
Require Import JetStartupReview.jet_clight_forward.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.




Lemma elements_sizeof_confAmount : sizeof (Clight.genv_cenv elements_ge) (Tstruct _confAmount noattr) = 40.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_assetIssuance_union' : elements_field_at _assetIssuance _anon_union 0.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_issuance_union_new' : elements_union_field_at __4839 _anon_union 0.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_issuance_tokenAmt : elements_field_at __4840 _tokenAmt 32.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_issuanceTokenAmt_symbol :
  Genv.find_symbol (Clight.genv_genv elements_ge) _issuanceTokenAmt =
    Some (elements_symbol_block _issuanceTokenAmt).
Proof. vm_compute; reflexivity. Qed.
Lemma elements_issuanceTokenAmt_funct :
  Genv.find_funct (Clight.genv_genv elements_ge)
    (Vptr (elements_symbol_block _issuanceTokenAmt) Ptrofs.zero) = Some (Internal f_issuanceTokenAmt).
Proof. vm_compute; reflexivity. Qed.

Lemma bool_val_of_bool (b : bool) m : bool_val (Val.of_bool b) tint m = Some b.
Proof. destruct b; reflexivity. Qed.

(** Cells: a tag bit, then the token amount of a new issuance, an explicit
    zero for a reissuance, or padding when there is no issuance. *)
Definition token_cells (ty pfx : int) (xs : list int) (v : int64) : list Cell :=
  issuance_tagged_cells (negb (Int.eq (Int.repr 0) ty)) 258
    (if Int.eq (Int.repr 1) ty then amt_cells pfx xs v else amt_cells (Int.repr 1) xs Int64.zero).

Definition token_then : statement :=
  match fn_body f_issuanceTokenAmt with
  | Ssequence _ (Sifthenelse _ s _) => s
  | _ => Sskip
  end.

Definition token_env (bc : block) : env :=
  PTree.set ___compound (bc, Tstruct _confAmount noattr) empty_env.

Ltac gso1 := rewrite PTree.gso by discriminate.

(** The present branch: select the amount record (the issuance's token
    amount, or the local explicit zero), then [amt]. *)
Lemma exec_token_then le mb bc bi ibase bf base bw edge cur ty xs v pfx :
  le!_dst = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_issuance = Some (Vptr bi (Ptrofs.repr ibase)) ->
  length xs = 8%nat -> 0 <= ibase -> ibase + 280 <= Ptrofs.max_unsigned ->
  bc <> bf -> bc <> bw -> bc <> bi ->
  Mem.range_perm mb bc 0 40 Cur Writable ->
  out_sep bf base bw edge cur 258 bi ibase (ibase + 280) ->
  Mem.load Mint32 mb bi (ibase + 272) = Some (Vint ty) ->
  (Int.eq (Int.repr 1) ty = true ->
     Mem.load Mint32 mb bi (ibase + 32 + 32) = Some (Vint pfx) /\
     (Int.eq (Int.repr 1) pfx = true -> Mem.load Mint64 mb bi (ibase + 32) = Some (Vlong v)) /\
     (Int.eq (Int.repr 1) pfx = false -> uint32_array_at mb bi (ibase + 32) xs)) ->
  write_frame_at mb bf base bw edge cur 258 ->
  exists le' ms me,
    Clight2.exec_stmt elements_ge (token_env bc) le mb token_then E0 le' me Out_normal /\
    (forall chunk b ofs, b <> bc -> Mem.load chunk ms b ofs = Mem.load chunk mb b ofs) /\
    (forall b ofs kind p, Mem.perm mb b ofs kind p -> Mem.perm ms b ofs kind p) /\
    (forall b, Mem.valid_block mb b -> Mem.valid_block ms b) /\
    write_effect ms me bf base bw edge cur 258
      (if Int.eq (Int.repr 1) ty then amt_cells pfx xs v else amt_cells (Int.repr 1) xs Int64.zero).
Proof.
  intros HD HI HL H0 HM Ncf Ncw Nci HPc HSep HT HNew HF.
  set (e := token_env bc).
  set (le3 := PTree.set _t'3 (Vint ty) le).
  assert (HD3 : le3!_dst = Some (Vptr bf (Ptrofs.repr base))) by (unfold le3; gso1; exact HD).
  assert (HI3 : le3!_issuance = Some (Vptr bi (Ptrofs.repr ibase))) by (unfold le3; gso1; exact HI).
  assert (HSet3 : Clight2.exec_stmt elements_ge e le mb
    (Sset _t'3 (Efield (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr)))
      (Tstruct _assetIssuance noattr)) _type tint)) E0 le3 mb Out_normal).
  { apply exec_set.
    eapply eval_elements_field_value with (sid := _assetIssuance) (delta := 272) (chunk := Mint32).
    - reflexivity.
    - exact elements_assetIssuance_type.
    - reflexivity.
    - apply eval_elements_deref_struct. exact HI.
    - rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HT]. }
  assert (HCond : eval_expr elements_ge e le3 mb
    (Ebinop Oeq (Econst_int (Int.repr 1) tint) (Etempvar _t'3 tint) tint)
    (Val.of_bool (Int.eq (Int.repr 1) ty))).
  { eapply eval_Ebinop with (v1 := Vint (Int.repr 1)) (v2 := Vint ty).
    - apply eval_Econst_int.
    - apply eval_Etempvar. unfold le3. apply PTree.gss.
    - apply elements_eq_cmp. }
  assert (HAmtCall : forall le4 mm me bq qofs,
    le4!_dst = Some (Vptr bf (Ptrofs.repr base)) -> le4!_t'1 = Some (Vptr bq (Ptrofs.repr qofs)) ->
    Clight2.eval_funcall elements_ge mm (Internal f_amt)
      [Vptr bf (Ptrofs.repr base); Vptr bq (Ptrofs.repr qofs)] E0 me Vundef ->
    Clight2.exec_stmt elements_ge e le4 mm
      (Scall None
        (Evar _amt (Tfunction (Tcons (tptr (Tstruct _frameItem noattr))
          (Tcons (tptr (Tstruct _confAmount noattr)) Tnil)) tvoid cc_default))
        [Etempvar _dst (tptr (Tstruct _frameItem noattr));
         Etempvar _t'1 (tptr (Tstruct _confAmount noattr))]) E0 le4 me Out_normal).
  { intros le4 mm me bq qofs Hd4 H14 HC.
    change le4 with (set_opttemp None Vundef le4) at 2.
    eapply exec_Scall with (vf := Vptr (elements_symbol_block _amt) Ptrofs.zero) (f := Internal f_amt)
      (vargs := [Vptr bf (Ptrofs.repr base); Vptr bq (Ptrofs.repr qofs)]) (vres := Vundef).
    - reflexivity.
    - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact elements_amt_symbol]|
        apply deref_loc_reference; reflexivity].
    - eapply eval_Econs; [apply eval_Etempvar; exact Hd4|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; exact H14|reflexivity|apply eval_Enil].
    - exact elements_amt_funct.
    - reflexivity.
    - exact HC. }
  destruct (Int.eq (Int.repr 1) ty) eqn:HNewB.
  - (* new issuance: the token amount of the record *)
    destruct (HNew eq_refl) as (HP & HV & HA).
    assert (HSepA : out_sep bf base bw edge cur 258 bi (ibase + 32) (ibase + 32 + 40)).
    { eapply out_sep_range; [exact HSep|lia|lia]. }
    destruct (eval_elements_amt_layout mb bi (ibase + 32) bf base bw edge cur xs v pfx HL
      ltac:(lia) ltac:(lia) HSepA HV HA HP HF) as (me & HC & E).
    set (le4 := PTree.set _t'1 (Vptr bi (Ptrofs.repr (ibase + 32))) le3).
    exists le4, mb, me.
    split; [|split; [intros; reflexivity|split; [auto|split; [auto|exact E]]]].
    unfold token_then, f_issuanceTokenAmt; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le4).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le3); [exact HSet3|].
      eapply exec_Sifthenelse with (v1 := Val.of_bool true) (b := true);
        [exact HCond|reflexivity|].
      apply exec_set. eapply eval_Ecast with (v1 := Vptr bi (Ptrofs.repr (ibase + 32))); [|reflexivity].
      eapply eval_Eaddrof.
      rewrite <- (elements_ptr_add_repr ibase 32) by lia.
      eapply eval_elements_field_lvalue; [reflexivity|exact elements_issuance_tokenAmt|].
      rewrite <- (Ptrofs.add_zero (Ptrofs.repr ibase)).
      eapply eval_Elvalue; [|apply deref_loc_copy; reflexivity].
      eapply eval_elements_union_field_lvalue; [reflexivity|exact elements_issuance_union_new'|].
      rewrite <- (Ptrofs.add_zero (Ptrofs.repr ibase)).
      eapply eval_Elvalue; [|apply deref_loc_copy; reflexivity].
      eapply eval_elements_field_lvalue; [reflexivity|exact elements_assetIssuance_union'|].
      apply eval_elements_deref_struct. exact HI3.
    + eapply HAmtCall with (bq := bi) (qofs := ibase + 32); [|unfold le4; apply PTree.gss|exact HC].
      unfold le4. gso1. exact HD3.
  - (* reissuance: the local explicit zero *)
    assert (HEc : e!___compound = Some (bc, Tstruct _confAmount noattr)) by (unfold e, token_env; apply PTree.gss).
    assert (HCv : forall le' mm, eval_expr elements_ge e le' mm
      (Evar ___compound (Tstruct _confAmount noattr)) (Vptr bc Ptrofs.zero)).
    { intros le' mm. eapply eval_Elvalue; [apply eval_Evar_local; exact HEc|apply deref_loc_copy; reflexivity]. }
    destruct (Mem.valid_access_store mb Mint64 bc 0 (Vlong (Int64.repr 0))) as [ms1 HS1].
    { split; [intros o Ho; apply HPc; cbn in Ho; lia|apply Z.divide_0_r]. }
    destruct (Mem.valid_access_store ms1 Mint32 bc 32 (Vint (Int.repr 1))) as [ms2 HS2].
    { split; [intros o Ho; eapply Mem.perm_store_1; [exact HS1|]; apply HPc; cbn in Ho; lia|exists 8; reflexivity]. }
    assert (HLs : forall chunk b ofs, b <> bc -> Mem.load chunk ms2 b ofs = Mem.load chunk mb b ofs).
    { intros chunk b ofs Hb.
      rewrite (Mem.load_store_other _ _ _ _ _ _ HS2) by (left; exact Hb).
      exact (Mem.load_store_other _ _ _ _ _ _ HS1 chunk b ofs (or_introl Hb)). }
    assert (HPs : forall b ofs kind p, Mem.perm mb b ofs kind p -> Mem.perm ms2 b ofs kind p).
    { intros b ofs kind p H. eapply Mem.perm_store_1; [exact HS2|]. eapply Mem.perm_store_1; eauto. }
    assert (HVs : forall b, Mem.valid_block mb b -> Mem.valid_block ms2 b).
    { intros b H. eapply Mem.store_valid_block_1; [exact HS2|]. eapply Mem.store_valid_block_1; eauto. }
    assert (HFs : write_frame_at ms2 bf base bw edge cur 258).
    { eapply write_frame_at_preserved; [|exact HPs|exact HF].
      intros chunk b ofs v' Hb Hl. rewrite HLs; [exact Hl|].
      destruct Hb; subst; apply not_eq_sym; assumption. }
    assert (HV0 : Mem.load Mint64 ms2 bc 0 = Some (Vlong Int64.zero)).
    { rewrite (Mem.load_store_other _ _ _ _ _ _ HS2) by (right; left; cbn; lia).
      exact (Mem.load_store_same _ _ _ _ _ _ HS1). }
    assert (HP0 : Mem.load Mint32 ms2 bc (0 + 32) = Some (Vint (Int.repr 1))).
    { exact (Mem.load_store_same _ _ _ _ _ _ HS2). }
    assert (HSepC : out_sep bf base bw edge cur 258 bc 0 (0 + 40)).
    { split; left; assumption. }
    destruct (eval_elements_amt_layout ms2 bc 0 bf base bw edge cur xs Int64.zero (Int.repr 1) HL
      ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) HSepC
      (fun _ => HV0) ltac:(intro Hx; discriminate Hx) HP0 HFs) as (me & HC & E).
    set (le4 := PTree.set _t'1 (Vptr bc (Ptrofs.repr 0)) le3).
    exists le4, ms2, me.
    split; [|split; [exact HLs|split; [exact HPs|split; [exact HVs|exact E]]]].
    unfold token_then, f_issuanceTokenAmt; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms2) (le1 := le4).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le3); [exact HSet3|].
      eapply exec_Sifthenelse with (v1 := Val.of_bool false) (b := false);
        [exact HCond|reflexivity|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms2) (le1 := le3).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms1) (le1 := le3).
        -- eapply exec_Sassign with (v2 := Vint (Int.repr 0)) (v := Vlong (Int64.repr 0))
             (loc := bc) (ofs := Ptrofs.add (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)) (Ptrofs.repr 0)).
           ++ eapply eval_elements_union_field_lvalue; [reflexivity|exact elements_confAmount_explicit|].
              eapply eval_Elvalue; [|apply deref_loc_copy; reflexivity].
              eapply eval_elements_field_lvalue; [reflexivity|exact elements_confAmount_union|].
              apply HCv.
           ++ apply eval_Econst_int.
           ++ apply elements_cast_const'. lia.
           ++ eapply assign_loc_value; [reflexivity|].
              change (Ptrofs.add (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)) (Ptrofs.repr 0)) with Ptrofs.zero.
              exact HS1.
        -- eapply exec_Sassign with (v2 := Vint (Int.repr 1)) (v := Vint (Int.repr 1))
             (loc := bc) (ofs := Ptrofs.add Ptrofs.zero (Ptrofs.repr 32)).
           ++ eapply eval_elements_field_lvalue; [reflexivity|exact elements_confAmount_prefix|].
              apply HCv.
           ++ apply eval_Econst_int.
           ++ reflexivity.
           ++ eapply assign_loc_value; [reflexivity|].
              change (Ptrofs.add Ptrofs.zero (Ptrofs.repr 32)) with (Ptrofs.repr 32).
              exact HS2.
      * apply exec_set. eapply eval_Ecast with (v1 := Vptr bc Ptrofs.zero); [|reflexivity].
        eapply eval_Eaddrof. apply eval_Evar_local. exact HEc.
    + eapply HAmtCall with (bq := bc) (qofs := 0); [|unfold le4; apply PTree.gss|exact HC].
      unfold le4. gso1. exact HD3.
Qed.
