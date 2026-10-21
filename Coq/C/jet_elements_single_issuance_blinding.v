(** Active issuance's real blinding/entropy branches. The new path executes
    the zero-array initializer, then hashes the contract; the reissuance path
    reads only its active nonce and entropy fields. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_read8s_layout C.jet_bitmachine_rep.
Require Import C.jet_buffer_input.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_elements_prim C.jet_elements_field_eval C.jet_elements_amt_helper.
Require Import C.jet_elements_single_issuance_prep C.jet_elements_single_issuance_amount.
Require Import C.jet_elements_single_issuance_none C.jet_elements_issuance_zero_array.
Require Import C.jet_elements_env_tx_calls C.jet_elements_conf_hash_bridge.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_support_sha_uchars_prep.
Require Import C.jet_elements_support_sha_uchars_exec C.jet_elements_support_sha_be32_write.
Require Import C.jet_elements_support_sha_be64_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.
Local Notation ISS := (Tstruct _assetIssuance noattr).

Definition eis_union_hash_addr (isnew : bool) : expr :=
  Eaddrof (Efield
    (Efield (eis_issuance_field _anon_union (Tunion __4839 noattr))
      (if isnew then _anon_union else 19015305760020270911%positive)
      (Tstruct (if isnew then __4840 else __4841) noattr))
    (if isnew then _contractHash else _blindingNonce) MID) (tptr MID).
Definition eis_hash_addr_stmt (source : expr) : statement :=
  Scall None (Evar _sha256_hash (Tfunction (Tcons CTXP (Tcons (tptr MID) Tnil)) tvoid cc_default))
    [Eaddrof (Evar _ctx CTX) CTXP; source].

Lemma eis_reissuance_arm_offset : elements_union_field_at __4839 19015305760020270911%positive 0.
Proof. vm_compute; reflexivity. Qed.
Lemma eis_contract_offset : elements_field_at __4840 _contractHash 0.
Proof. vm_compute; reflexivity. Qed.
Lemma eis_nonce_offset : elements_field_at __4841 _blindingNonce 0.
Proof. vm_compute; reflexivity. Qed.
Lemma eis_entropy_offset : elements_field_at _assetIssuance _entropy 72.
Proof. vm_compute; reflexivity. Qed.

Lemma eval_eis_union_hash_addr isnew e le m bin ofs :
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  eval_expr sha_ge e le m (eis_union_hash_addr isnew) (Vptr bin (Ptrofs.repr ofs)).
Proof.
  intros HI. unfold eis_union_hash_addr. eapply eval_Eaddrof.
  replace (Ptrofs.repr ofs) with
    (Ptrofs.add (Ptrofs.add (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr 0))
      (Ptrofs.repr 0)) (Ptrofs.repr 0))
    by (change (Ptrofs.repr 0) with Ptrofs.zero; rewrite !Ptrofs.add_zero; reflexivity).
  eapply eval_elements_field_lvalue; [reflexivity| |].
  { destruct isnew; [exact eis_contract_offset|exact eis_nonce_offset]. }
  eapply eval_Elvalue.
  - eapply eval_elements_union_field_lvalue; [reflexivity| |].
    { destruct isnew; [exact eis_issuance_new_offset|exact eis_reissuance_arm_offset]. }
    eapply eval_Elvalue.
    + eapply eval_elements_field_lvalue; [reflexivity|exact eis_issuance_union_offset|].
      apply eval_elements_deref_struct. exact HI.
    + apply deref_loc_copy; reflexivity.
  - apply deref_loc_copy; reflexivity.
Qed.

Definition eis_blinding_stmt : statement :=
  ltac:(let s := eval cbv delta [eis_some] beta iota in eis_some in
    let rec seek s := lazymatch s with
      | Ssequence (Sset _t'5 _) _ => exact s
      | Ssequence ?l ?r => first [seek l | seek r]
      end in seek s).
Definition eis_new_blinding : statement :=
  ltac:(let s := eval cbv delta [eis_blinding_stmt] beta iota in eis_blinding_stmt in
    lazymatch s with Ssequence _ (Sifthenelse _ ?n _) => exact n end).
Definition eis_re_blinding : statement :=
  ltac:(let s := eval cbv delta [eis_blinding_stmt] beta iota in eis_blinding_stmt in
    lazymatch s with Ssequence _ (Sifthenelse _ _ ?r) => exact r end).
Definition eis_zero_uchars_stmt : statement :=
  Scall None (Evar _sha256_uchars
    (Tfunction (Tcons CTXP (Tcons (tptr tuchar) (Tcons tulong Tnil))) tbool cc_default))
    [Eaddrof (Evar _ctx CTX) CTXP; Evar ___compound__3 (tarray tuchar 32);
      Econst_int (Int.repr 32) tint].

Lemma eis_blinding_shape : eis_blinding_stmt =
  Ssequence (Sset _t'5 (eis_issuance_field _type tint))
    (Sifthenelse (Ebinop Oeq (Econst_int Int.one tint) (Etempvar _t'5 tint) tint)
      eis_new_blinding eis_re_blinding).
Proof. reflexivity. Qed.
Lemma eis_new_blinding_shape : eis_new_blinding =
  Ssequence (Ssequence eis_array_init_actual eis_zero_uchars_stmt)
    (eis_hash_addr_stmt (eis_union_hash_addr true)).
Proof. reflexivity. Qed.
Lemma eis_re_blinding_shape : eis_re_blinding =
  Ssequence (eis_hash_addr_stmt (eis_union_hash_addr false)) (eis_hash_stmt _entropy).
Proof. reflexivity. Qed.

Definition eis_blinding_bytes (isnew : bool) (q ent : hash256) : list int :=
  if isnew then repeat Int.zero 32 ++ be_bytes (hash256_reg q)
  else be_bytes (hash256_reg q) ++ be_bytes (hash256_reg ent).

Definition eis_blinding_pair (isnew : bool) (q ent : hash256) : Ty.tySem (Ty.Prod Word256 Word256) :=
  if isnew then (@fromZ (WordToZ 8) 0, from_hash256 q)
  else (from_hash256 q, from_hash256 ent).

Lemma eis_zero256_bytes :
  map word8_array_value (vector_values Word8 5 (@fromZ (WordToZ 8) 0)) = repeat Int.zero 32.
Proof. vm_compute; reflexivity. Qed.

Lemma eis_blinding_bytes_canonical isnew q ent :
  eis_blinding_bytes isnew q ent =
    map word8_array_value (vector_values Word8 6 (eis_blinding_pair isnew q ent)).
Proof.
  destruct isnew.
  - change (repeat Int.zero 32 ++ be_bytes (hash256_reg q) =
      map word8_array_value (vector_values Word8 5 (@fromZ (WordToZ 8) 0) ++
        vector_values Word8 5 (from_hash256 q))).
    rewrite map_app, eis_zero256_bytes, <- elements_hash_words_bytes. reflexivity.
  - change (be_bytes (hash256_reg q) ++ be_bytes (hash256_reg ent) =
      map word8_array_value (vector_values Word8 5 (from_hash256 q) ++
        vector_values Word8 5 (from_hash256 ent))).
    rewrite map_app, <- !elements_hash_words_bytes. reflexivity.
Qed.

Lemma eis_blinding_bytes_length isnew q ent : length (eis_blinding_bytes isnew q ent) = 64%nat.
Proof.
  unfold eis_blinding_bytes. destruct isnew;
    rewrite app_length, ?repeat_length, !be_bytes_length, !hash256_len; reflexivity.
Qed.

Section Blinding.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem exec_eis_zero_absorb e le m bb l regs c ovf :
  ctxi m bx bm l regs c ovf ->
  e!_ctx = Some (bx, CTX) -> e!___compound__3 = Some (bb, tarray tuchar 32) ->
  e!_sha256_uchars = None -> bb <> bx -> bb <> bm -> bb <> GC -> bb <> GM ->
  Mem.range_perm m bb 0 32 Cur Writable ->
  exists mf ovf',
    Clight2.exec_stmt sha_ge e le m (Ssequence eis_array_init_actual eis_zero_uchars_stmt)
      E0 le mf Out_normal /\
    ctxi mf bx bm (fst (absorb_i l regs (repeat Int.zero 32)))
      (snd (absorb_i l regs (repeat Int.zero 32))) (Int64.add c (Int64.repr 32)) ovf' /\
    (forall ch b o, Mem.valid_block m b -> b <> bb -> b <> bx -> b <> bm ->
      Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HX HC HB HG Hbx Hbm Hbg Hbc HP.
  destruct (exec_eis_zero_array_prefix e le ___compound__3 bb 32 HB ltac:(lia) m HP)
    as (mi & CI & HZ & LI & PI & VI).
  assert (XI : ctxi mi bx bm l regs c ovf).
  { eapply ctxi_other; [exact HX| |].
    - intros ch b o H. rewrite LI; [reflexivity|].
      left. destruct H as [H|[H|[H|H]]]; congruence.
    - intros b o k p _ P. apply PI, P. }
  assert (HZB : forall j, (j < length (repeat Int.zero 32))%nat ->
    Mem.load Mint8unsigned mi bb (Ptrofs.unsigned Ptrofs.zero + Z.of_nat j) =
      Some (Vint (nth j (repeat Int.zero 32) Int.zero))).
  { intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat.
    change (Ptrofs.unsigned Ptrofs.zero) with 0. rewrite Z.add_0_l. apply HZ, Hj. }
  destruct (ctxi_uchars bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mi bb Ptrofs.zero
    l regs (repeat Int.zero 32) c ovf XI Hbx Hbm
    ltac:(rewrite repeat_length; change (0 + 32 <= 18446744073709551615); lia) HZB)
    as (mf & CF & XF & LF & PF & VF).
  rewrite repeat_length in CF, XF.
  match type of XF with ctxi _ _ _ _ _ _ ?v => exists mf, v end.
  split.
  { rewrite eis_zero_array_shape. eapply exec_Sseq_1 with
      (t1 := E0) (t2 := E0) (le1 := le) (m1 := mi); [exact CI|].
    unfold eis_zero_uchars_stmt.
    match type of CF with Clight2.eval_funcall _ _ _ _ _ _ ?v =>
      change le with (set_opttemp None v le) at 2 end.
    eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
      (vargs := [Vptr bx Ptrofs.zero; Vptr bb Ptrofs.zero; Vlong (Int64.repr 32)])
      (f := Internal f_sha256_uchars).
    - reflexivity.
    - eapply eval_Elvalue; [apply eval_Evar_global; [exact HG|exact sha_uchars_symbol]|].
      apply deref_loc_reference; reflexivity.
    - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact HC|reflexivity|].
      eapply eval_Econs; [eapply eval_Elvalue; [apply eval_Evar_local; exact HB|
        apply deref_loc_reference; reflexivity]|reflexivity|].
      eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
    - exact sha_uchars_funct.
    - reflexivity.
    - exact CF. }
  split; [exact XF|]. split.
  { intros ch b o V Nb Nx Nm. rewrite LF by auto. apply LI; left; exact Nb. }
  split.
  { intros b o k p V P. apply PF; [auto|apply PI, P]. }
  intros b V. apply VF, VI, V.
Qed.

Theorem exec_eis_blinding (isnew : bool) e le m bin ofs bb q ent l regs c ovf :
  ctxi m bx bm l regs c ovf ->
  e!_ctx = Some (bx, CTX) -> e!___compound__3 = Some (bb, tarray tuchar 32) ->
  e!_sha256_uchars = None -> e!_sha256_hash = None ->
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned -> bin <> bx -> bin <> bm ->
  bb <> bin -> bb <> bx -> bb <> bm -> bb <> GC -> bb <> GM ->
  Mem.load Mint32 m bin (ofs + 272) = Some (Vint (eis_kind isnew)) ->
  uint32_array_at m bin ofs (hash256_reg q) ->
  (isnew = false -> uint32_array_at m bin (ofs + 72) (hash256_reg ent)) ->
  Mem.range_perm m bb 0 32 Cur Writable ->
  exists mf ovf',
    Clight2.exec_stmt sha_ge e le m eis_blinding_stmt E0
      (PTree.set _t'5 (Vint (eis_kind isnew)) le) mf Out_normal /\
    ctxi mf bx bm (fst (absorb_i l regs (eis_blinding_bytes isnew q ent)))
      (snd (absorb_i l regs (eis_blinding_bytes isnew q ent))) (Int64.add c (Int64.repr 64)) ovf' /\
    (forall ch b o, Mem.valid_block m b -> b <> bb -> b <> bx -> b <> bm ->
      Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HX HC HB HU HH HI HO HM Hix Him Hbi Hbx Hbm Hbg Hbc HT HQ HE HP.
  set (le1 := PTree.set _t'5 (Vint (eis_kind isnew)) le).
  assert (ET : Clight2.exec_stmt sha_ge e le m (Sset _t'5 (eis_issuance_field _type tint))
    E0 le1 m Out_normal).
  { apply exec_Sset. eapply eval_eis_kind; eassumption. }
  assert (EC : eval_expr sha_ge e le1 m
    (Ebinop Oeq (Econst_int Int.one tint) (Etempvar _t'5 tint) tint) (Val.of_bool isnew)).
  { eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; unfold le1; apply PTree.gss|].
    destruct isnew; reflexivity. }
  assert (HI1 : le1!_issuance = Some (Vptr bin (Ptrofs.repr ofs))).
  { unfold le1. rewrite PTree.gso by discriminate. exact HI. }
  assert (VB : Mem.valid_block m bin).
  { assert (HL : Mem.load Mint32 m bin (ofs + 4 * Z.of_nat 0) =
      Some (Vint (nth 0 (hash256_reg q) Int.zero))).
    { apply HQ, nth_error_nth'. rewrite hash256_len. lia. }
    eapply load_valid_block; exact HL. }
  destruct isnew.
  - destruct (exec_eis_zero_absorb e le1 m bb l regs c ovf HX HC HB HU Hbx Hbm Hbg Hbc HP)
      as (mz & vz & CZ & XZ & LZ & PZ & VZ).
    assert (HQZ : forall j, (j < 8)%nat ->
      Mem.load Mint32 mz bin (Ptrofs.unsigned (Ptrofs.repr ofs) + 4 * Z.of_nat j) =
        Some (Vint (nth j (hash256_reg q) Int.zero))).
    { intros j Hj. rewrite Ptrofs.unsigned_repr by lia.
      rewrite LZ by (auto using not_eq_sym). apply HQ, nth_error_nth'.
      rewrite hash256_len. exact Hj. }
    destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mz bin (Ptrofs.repr ofs)
      _ _ (hash256_reg q) _ _ XZ (hash256_len q)
      ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) HQZ)
      as (mf & CF & XF & LF & PF & VF).
    rewrite <- absorb_i_app, Int64.add_assoc in XF.
    change (Int64.add (Int64.repr 32) (Int64.repr 32)) with (Int64.repr 64) in XF.
    match type of XF with ctxi _ _ _ _ _ _ ?v => exists mf, v end.
    split.
    { rewrite eis_blinding_shape. eapply exec_Sseq_1 with
        (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m); [exact ET|].
      eapply exec_Sifthenelse with (v1 := Val.of_bool true) (b := true);
        [exact EC|reflexivity|].
      rewrite eis_new_blinding_shape. eapply exec_Sseq_1 with
        (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mz); [exact CZ|].
      eapply mt_call_hash; [exact HH|exact HC| |reflexivity|exact CF].
      apply eval_eis_union_hash_addr. exact HI1. }
    split; [exact XF|]. split.
    { intros ch b o V Nb Nx Nm. rewrite LF by auto. apply LZ; assumption. }
    split.
    { intros b o k p V P. apply PF; [auto|]. apply PZ; assumption. }
    intros b V. apply VF, VZ, V.
  - assert (HQ0 : forall j, (j < 8)%nat ->
      Mem.load Mint32 m bin (Ptrofs.unsigned (Ptrofs.repr ofs) + 4 * Z.of_nat j) =
        Some (Vint (nth j (hash256_reg q) Int.zero))).
    { intros j Hj. rewrite Ptrofs.unsigned_repr by lia.
      apply HQ, nth_error_nth'. rewrite hash256_len. exact Hj. }
    destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m bin (Ptrofs.repr ofs)
      _ _ (hash256_reg q) _ _ HX (hash256_len q)
      ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) HQ0)
      as (mq & CQ & XQ & LQ & PQ & VQ).
    assert (HEQ : forall j, (j < 8)%nat ->
      Mem.load Mint32 mq bin (Ptrofs.unsigned (Ptrofs.repr (ofs + 72)) + 4 * Z.of_nat j) =
        Some (Vint (nth j (hash256_reg ent) Int.zero))).
    { intros j Hj. rewrite Ptrofs.unsigned_repr by lia. rewrite LQ by assumption.
      apply (HE eq_refl), nth_error_nth'. rewrite hash256_len. exact Hj. }
    destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mq bin (Ptrofs.repr (ofs + 72))
      _ _ (hash256_reg ent) _ _ XQ (hash256_len ent)
      ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) HEQ)
      as (mf & CF & XF & LF & PF & VF).
    rewrite <- absorb_i_app, Int64.add_assoc in XF.
    change (Int64.add (Int64.repr 32) (Int64.repr 32)) with (Int64.repr 64) in XF.
    match type of XF with ctxi _ _ _ _ _ _ ?v => exists mf, v end.
    split.
    { rewrite eis_blinding_shape. eapply exec_Sseq_1 with
        (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m); [exact ET|].
      eapply exec_Sifthenelse with (v1 := Val.of_bool false) (b := false);
        [exact EC|reflexivity|].
      rewrite eis_re_blinding_shape. eapply exec_Sseq_1 with
        (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mq).
      - eapply mt_call_hash; [exact HH|exact HC| |reflexivity|exact CQ].
        apply eval_eis_union_hash_addr. exact HI1.
      - eapply eis_hash_stmt_exec; [exact eis_entropy_offset|lia|lia|exact HO|exact HM|
          exact HH|exact HC|exact HI1|exact CF]. }
    split; [exact XF|]. split.
    { intros ch b o V _ Nx Nm. rewrite LF by auto. apply LQ; assumption. }
    split.
    { intros b o k p V P. apply PF; [auto|]. apply PQ; assumption. }
    intros b V. apply VF, VQ, V.
Qed.
End Blinding.
