(** The real confidential compound literal used for both issuance IDs:
    typed 32-byte struct copy, then EXPLICIT prefix. No libc call is modeled
    for Clight's By_copy assignment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Digest.
Require Import C.jet_exec C.jet_uint32_array_init C.jet_struct_copy_loads.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_elements_field_eval C.jet_elements_asset_helper C.jet_elements_asset_jets C.jet_elements_prim.
Require Import C.jet_elements_support_sha_linkage.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.
Local Notation CONF := (Tstruct _confidential noattr).
Local Notation MID := (Tstruct _sha256_midstate noattr).

Lemma eis_words_readable m b base xs :
  length xs = 8%nat -> uint32_array_at m b base xs ->
  Mem.range_perm m b base (base + 32) Cur Readable.
Proof.
  intros HLen HW off HO.
  set (q := (off - base) / 4).
  assert (Hq0 : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  assert (Hq8 : q < 8) by (unfold q; apply Z.div_lt_upper_bound; lia).
  assert (HJ : (Z.to_nat q < length xs)%nat) by (rewrite HLen; lia).
  assert (HL : Mem.load Mint32 m b (base + 4 * Z.of_nat (Z.to_nat q)) =
    Some (Vint (nth (Z.to_nat q) xs Int.zero))).
  { apply HW, nth_error_nth'. exact HJ. }
  pose proof (proj1 (Mem.load_valid_access _ _ _ _ _ HL)) as HP.
  apply HP. change (size_chunk Mint32) with 4.
  rewrite Z2Nat.id by exact Hq0.
  pose proof (Z.div_mod (off - base) 4 ltac:(lia)) as HD.
  pose proof (Z.mod_pos_bound (off - base) 4 ltac:(lia)) as HR.
  fold q in HD. lia.
Qed.

Definition eis_asset_literal_stmt (id : ident) (source : expr) : statement :=
  Ssequence
    (Sassign (Efield (Evar id CONF) _data MID) source)
    (Sassign (Efield (Evar id CONF) _prefix tint) (Econst_int Int.one tint)).

Lemma eis_mid_size : sizeof (Clight.genv_cenv sha_ge) MID = 32.
Proof. vm_compute; reflexivity. Qed.
Lemma eis_mid_align : alignof_blockcopy (Clight.genv_cenv sha_ge) MID = 4.
Proof. vm_compute; reflexivity. Qed.

Definition eis_asset_init_actual : statement :=
  ltac:(let body := eval cbv delta [f_simplicity_issuance_hash fn_body] beta iota in
      (fn_body f_simplicity_issuance_hash) in
    let rec seek s :=
      lazymatch s with
      | Ssequence (Sassign (Efield (Evar ___compound _) _data _) _) _ => exact s
      | Ssequence ?l ?r => first [seek l | seek r]
      | Sifthenelse _ ?l ?r => first [seek l | seek r]
      end in seek body).

Definition eis_token_init_actual : statement :=
  ltac:(let body := eval cbv delta [f_simplicity_issuance_hash fn_body] beta iota in
      (fn_body f_simplicity_issuance_hash) in
    let rec seek s :=
      lazymatch s with
      | Ssequence (Sassign (Efield (Evar ___compound__1 _) _data _) _) _ => exact s
      | Ssequence ?l ?r => first [seek l | seek r]
      | Sifthenelse _ ?l ?r => first [seek l | seek r]
      end in seek body).

Lemma eis_asset_literal_shape :
  eis_asset_init_actual = eis_asset_literal_stmt ___compound
    (Efield (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr)))
      (Tstruct _assetIssuance noattr)) _assetId MID).
Proof. reflexivity. Qed.

Lemma eis_token_literal_shape :
  eis_token_init_actual = eis_asset_literal_stmt ___compound__1
    (Efield (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr)))
      (Tstruct _assetIssuance noattr)) _tokenId MID).
Proof. reflexivity. Qed.

Theorem exec_eis_asset_literal e le m id source bd bs base (h : hash256) :
  e!id = Some (bd, CONF) -> typeof source = MID ->
  eval_expr sha_ge e le m source (Vptr bs (Ptrofs.repr base)) ->
  bd <> bs -> 0 <= base -> base + 32 <= Ptrofs.max_unsigned ->
  uint32_array_at m bs base (hash256_reg h) ->
  Mem.range_perm m bd 0 36 Cur Writable ->
  exists mf,
    Clight2.exec_stmt sha_ge e le m (eis_asset_literal_stmt id source) E0 le mf Out_normal /\
    asset_rep mf bd 0 (Explicit h) /\
    (forall chunk b off, b <> bd \/ off + size_chunk chunk <= 0 \/ 36 <= off ->
      Mem.load chunk mf b off = Mem.load chunk m b off) /\
    (forall b off k p, Mem.perm m b off k p -> Mem.perm mf b off k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HE HT HSource Hne HB HM HW HP.
  assert (HR : Mem.range_perm m bs base (base + 32) Cur Readable).
  { apply eis_words_readable with (xs := hash256_reg h); [apply hash256_len|exact HW]. }
  destruct (Mem.range_perm_loadbytes m bs base 32 HR) as [bytes HL].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HL) as HLength.
  assert (HD : Mem.range_perm m bd 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLength. intros off Ho. apply HP; lia. }
  destruct (Mem.range_perm_storebytes m bd 0 bytes HD) as [mc HS].
  assert (HBC : Mem.loadbytes mc bd 0 32 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HS) as H.
    rewrite HLength in H. exact H. }
  assert (HPref : Mem.valid_access mc Mint32 bd 32 Writable).
  { split; [|change (4 | 32); exists 8; reflexivity].
    intros off Ho. eapply Mem.perm_storebytes_1; [exact HS|].
    apply HP. change (size_chunk Mint32) with 4 in Ho. lia. }
  destruct (Mem.valid_access_store mc Mint32 bd 32 (Vint Int.one) HPref) as [mf SP].
  assert (HAlign : (4 | base)).
  { assert (HL0 : Mem.load Mint32 m bs (base + 4 * Z.of_nat 0) =
      Some (Vint (nth 0 (hash256_reg h) Int.zero))).
    { apply HW, nth_error_nth'. rewrite hash256_len. lia. }
    pose proof (proj2 (Mem.load_valid_access _ _ _ _ _ HL0)) as HA.
    change (4 | base + 4 * Z.of_nat 0) in HA.
    replace (base + 4 * Z.of_nat 0) with base in HA by lia. exact HA. }
  assert (HObj : forall mm,
    eval_expr sha_ge e le mm (Evar id CONF) (Vptr bd Ptrofs.zero)).
  { intros mm. eapply eval_Elvalue; [apply eval_Evar_local; exact HE|].
    apply deref_loc_copy; reflexivity. }
  exists mf. split.
  { unfold eis_asset_literal_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    - eapply exec_Sassign_copy.
      + change Ptrofs.zero with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)).
        eapply eval_elements_field_lvalue; [reflexivity|exact elements_confidential_data|apply HObj].
      + exact HSource.
      + rewrite HT. reflexivity.
      + eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr base) (bytes := bytes); cbn [typeof].
        * reflexivity.
        * intros _. rewrite eis_mid_align. rewrite Ptrofs.unsigned_repr by lia. exact HAlign.
        * intros _. rewrite eis_mid_align. change (4 | 0). exists 0; reflexivity.
        * left. intro E; apply Hne; symmetry; exact E.
        * rewrite eis_mid_size. rewrite Ptrofs.unsigned_repr by lia. exact HL.
        * exact HS.
    - eapply exec_Sassign_value with (v := Vint Int.one) (v2 := Vint Int.one)
        (b := bd) (ofs := Ptrofs.repr 32).
      + change (Ptrofs.repr 32) with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 32)).
        eapply eval_elements_field_lvalue; [reflexivity|exact elements_confidential_prefix|apply HObj].
      + constructor.
      + reflexivity.
      + apply assign_loc_value with (chunk := Mint32); [reflexivity|exact SP]. }
  split.
  { split.
    - intros j w HJ. unfold asset_words in HJ.
      assert (Hj : (j < 8)%nat).
      { rewrite <- (hash256_len h). apply nth_error_Some. rewrite HJ. discriminate. }
      rewrite (Mem.load_store_other _ _ _ _ _ _ SP).
      + eapply equal_loadbytes_field with (m1 := m) (b1 := bs) (base1 := base)
          (base2 := 0) (n := 32) (delta := 4 * Z.of_nat j) (bytes := bytes).
        * lia.
        * change (size_chunk Mint32) with 4. lia.
        * exact HL.
        * exact HBC.
        * change (4 | 0 + 4 * Z.of_nat j). exists (Z.of_nat j); lia.
        * exact (HW j w HJ).
      + right; left. change (size_chunk Mint32) with 4. lia.
    - exact (Mem.load_store_same _ _ _ _ _ _ SP). }
  split.
  { intros chunk b off HO. rewrite (Mem.load_store_other _ _ _ _ _ _ SP).
    - erewrite Mem.load_storebytes_other; [reflexivity|exact HS|].
      rewrite HLength. change (0 + 32) with 32. lia.
    - change (size_chunk Mint32) with 4. lia. }
  split.
  { intros b off k p P. eapply Mem.perm_store_1; [exact SP|].
    eapply Mem.perm_storebytes_1; eassumption. }
  intros b V. eapply Mem.store_valid_block_1; [exact SP|].
  eapply Mem.storebytes_valid_block_1; eassumption.
Qed.
