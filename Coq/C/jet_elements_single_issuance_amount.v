(** Actual asset amount call and token amount selection of issuance_hash.
    Reissuance constructs explicit zero locally and never reads tokenAmt. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_exec C.jet_memcpy_model C.jet_read8s_layout.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_elements_prim C.jet_elements_amount_jets C.jet_elements_amt_helper.
Require Import C.jet_elements_asset_jets.
Require Import C.jet_elements_conf_hash_repr C.jet_elements_conf_hash_bridge C.jet_elements_asset_amount_hash_spec.
Require Import C.jet_elements_field_eval C.jet_elements_issuance_helper C.jet_elements_input_utxo_prep.
Require Import C.jet_elements_issuance_zero_literal C.jet_elements_single_issuance_prep.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_support_sha_uchars_prep C.jet_elements_conf_amount_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.
Local Notation ISS := (Tstruct _assetIssuance noattr).
Local Notation AMT := (Tstruct _confAmount noattr).

Definition eis_issuance_field (field : ident) (t : type) : expr :=
  Efield (Ederef (Etempvar _issuance (tptr ISS)) ISS) field t.
Definition eis_token_amount_addr : expr :=
  Eaddrof (Efield
    (Efield (eis_issuance_field _anon_union (Tunion __4839 noattr))
      _anon_union (Tstruct __4840 noattr)) _tokenAmt AMT) (tptr AMT).
Definition eis_kind (isnew : bool) : int := if isnew then Int.one else Int.repr 2.
Definition eis_selected_amount (isnew : bool) (a : amountWith unit) : amountWith unit :=
  if isnew then a else Explicit Int64.zero.
Definition eis_conf_amount_stmt (source : expr) : statement :=
  Scall None (Evar _simplicity_sha256_confAmt
    (Tfunction (Tcons CTXP (Tcons (tptr AMT) Tnil)) tvoid cc_default))
    [Eaddrof (Evar _ctx CTX) CTXP; source].

Definition eis_asset_amount_stmt : statement :=
  ltac:(let s := eval cbv delta [eis_some] beta iota in eis_some in
    lazymatch s with Ssequence _ (Ssequence ?a _) => exact a end).
Definition eis_token_amount_stmt : statement :=
  ltac:(let s := eval cbv delta [eis_some] beta iota in eis_some in
    lazymatch s with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?t _))) => exact t end).
Definition eis_token_choose_stmt : statement :=
  Ssequence (Sset _t'6 (eis_issuance_field _type tint))
    (Sifthenelse (Ebinop Oeq (Econst_int Int.one tint) (Etempvar _t'6 tint) tint)
      (Sset _t'2 (Ecast eis_token_amount_addr (tptr AMT)))
      (Ssequence (eis_zero_init_stmt ___compound__2)
        (Sset _t'2 (Ecast (Eaddrof (Evar ___compound__2 AMT) (tptr AMT)) (tptr AMT))))).

Lemma eis_asset_amount_shape : eis_asset_amount_stmt =
  eis_conf_amount_stmt (Eaddrof (eis_issuance_field _assetAmt AMT) (tptr AMT)).
Proof. reflexivity. Qed.
Lemma eis_token_amount_shape : eis_token_amount_stmt =
  Ssequence eis_token_choose_stmt (eis_conf_amount_stmt (Etempvar _t'2 (tptr AMT))).
Proof. reflexivity. Qed.
Lemma eis_asset_amount_offset : elements_field_at _assetIssuance _assetAmt 232.
Proof. vm_compute; reflexivity. Qed.
Lemma eis_issuance_union_offset : elements_field_at _assetIssuance _anon_union 0.
Proof. vm_compute; reflexivity. Qed.
Lemma eis_issuance_new_offset : elements_union_field_at __4839 _anon_union 0.
Proof. vm_compute; reflexivity. Qed.
Lemma eis_new_token_offset : elements_field_at __4840 _tokenAmt 32.
Proof. vm_compute; reflexivity. Qed.

Lemma eval_eis_token_addr e le m bin ofs :
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned ->
  eval_expr sha_ge e le m eis_token_amount_addr (Vptr bin (Ptrofs.repr (ofs + 32))).
Proof.
  intros HI HO HM. unfold eis_token_amount_addr.
  eapply eval_Eaddrof. rewrite <- (elements_ptr_add_repr ofs 32) by lia.
  eapply eval_elements_field_lvalue; [reflexivity|exact eis_new_token_offset|].
  rewrite <- (elements_union_ofs ofs).
  eapply eval_Elvalue.
  - eapply eval_elements_union_field_lvalue; [reflexivity|exact eis_issuance_new_offset|].
    eapply eval_Elvalue.
    + eapply eval_elements_field_lvalue; [reflexivity|exact eis_issuance_union_offset|].
      apply eval_elements_deref_struct. exact HI.
    + apply deref_loc_copy; reflexivity.
  - apply deref_loc_copy; reflexivity.
Qed.

Lemma eval_eis_kind e le m bin ofs ty :
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned ->
  Mem.load Mint32 m bin (ofs + 272) = Some (Vint ty) ->
  eval_expr sha_ge e le m (eis_issuance_field _type tint) (Vint ty).
Proof.
  intros HI HO HM HT. eapply eval_elements_field_value;
    [reflexivity|exact elements_assetIssuance_type|reflexivity| |].
  - apply eval_elements_deref_struct. exact HI.
  - rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HT].
Qed.

Lemma exec_eis_conf_amount e le m mf source bx ba oa :
  e!_simplicity_sha256_confAmt = None -> e!_ctx = Some (bx, CTX) ->
  typeof source = tptr AMT -> eval_expr sha_ge e le m source (Vptr ba oa) ->
  Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confAmt)
    [Vptr bx Ptrofs.zero; Vptr ba oa] E0 mf Vundef ->
  Clight2.exec_stmt sha_ge e le m (eis_conf_amount_stmt source) E0 le mf Out_normal.
Proof.
  intros HG HC HT HA HCall. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_sha256_confAmt) Ptrofs.zero)
    (vargs := [Vptr bx Ptrofs.zero; Vptr ba oa]) (f := Internal f_simplicity_sha256_confAmt).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact HG|exact eiu_conf_amt_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact HC|reflexivity|].
    eapply eval_Econs; [exact HA|rewrite HT; reflexivity|apply eval_Enil].
  - exact eiu_conf_amt_funct.
  - reflexivity.
  - exact HCall.
Qed.

Definition eis_token_le (le : temp_env) (isnew : bool) (bin : block) (ofs : Z) (bz : block) : temp_env :=
  PTree.set _t'2 (if isnew then Vptr bin (Ptrofs.repr (ofs + 32)) else Vptr bz Ptrofs.zero)
    (PTree.set _t'6 (Vint (eis_kind isnew)) le).

Section Amounts.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem exec_eis_asset_amount e le m bin ofs a l regs c ovf :
  ctxi m bx bm l regs c ovf ->
  e!_ctx = Some (bx, CTX) -> e!_simplicity_sha256_confAmt = None ->
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned -> bin <> bx -> bin <> bm ->
  amount_rep m bin (ofs + 232) a ->
  let B := map word8_array_value (elements_amount_bytes (encode_amount a)) in
  exists mf,
    Clight2.exec_stmt sha_ge e le m eis_asset_amount_stmt E0 le mf Out_normal /\
    ctxi mf bx bm (fst (absorb_i l regs B)) (snd (absorb_i l regs B))
      (Int64.add c (Int64.repr (Z.of_nat (length B)))) (amt_overflow c ovf (conf_prefix a)) /\
    (forall ch b o, Mem.valid_block m b -> b <> bx -> b <> bm -> Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HX HC HG HI HO HM Hix Him HA B.
  destruct (eval_sha256_amount_repr Hmodel bx bm Hmx Hgx Hgm Hcx Hcm
    m l regs c ovf bin (ofs + 232) a HX ltac:(lia) Hix Him HA)
    as (mf & CF & XF & LF & PF & VF).
  exists mf. split.
  { rewrite eis_asset_amount_shape. eapply exec_eis_conf_amount;
      [exact HG|exact HC|reflexivity| |exact CF].
    eapply eval_Eaddrof. rewrite <- (elements_ptr_add_repr ofs 232) by lia.
    eapply eval_elements_field_lvalue; [reflexivity|exact eis_asset_amount_offset|].
    apply eval_elements_deref_struct. exact HI. }
  split; [exact XF|]. split; [exact LF|]. split; [exact PF|exact VF].
Qed.

Theorem exec_eis_token_amount (isnew : bool) e le m bin ofs bz a l regs c ovf :
  ctxi m bx bm l regs c ovf ->
  e!_ctx = Some (bx, CTX) -> e!_simplicity_sha256_confAmt = None ->
  e!___compound__2 = Some (bz, AMT) ->
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned ->
  bin <> bx -> bin <> bm -> bz <> bx -> bz <> bm -> bz <> GC -> bz <> GM ->
  Mem.load Mint32 m bin (ofs + 272) = Some (Vint (eis_kind isnew)) ->
  (isnew = true -> amount_rep m bin (ofs + 32) a) ->
  Mem.range_perm m bz 0 40 Cur Writable ->
  let v := eis_selected_amount isnew a in
  let B := map word8_array_value (elements_amount_bytes (encode_amount v)) in
  exists mf,
    Clight2.exec_stmt sha_ge e le m eis_token_amount_stmt E0 (eis_token_le le isnew bin ofs bz) mf Out_normal /\
    ctxi mf bx bm (fst (absorb_i l regs B)) (snd (absorb_i l regs B))
      (Int64.add c (Int64.repr (Z.of_nat (length B)))) (amt_overflow c ovf (conf_prefix v)) /\
    (forall ch b o, Mem.valid_block m b -> b <> bz -> b <> bx -> b <> bm ->
      Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HX HC HG HZ HI HO HM Hix Him Hzx Hzm Hzg Hzc HT HA HP v B.
  set (le1 := PTree.set _t'6 (Vint (eis_kind isnew)) le).
  assert (ET : Clight2.exec_stmt sha_ge e le m (Sset _t'6 (eis_issuance_field _type tint))
    E0 le1 m Out_normal).
  { apply exec_Sset. eapply eval_eis_kind; eassumption. }
  assert (EC : eval_expr sha_ge e le1 m
    (Ebinop Oeq (Econst_int Int.one tint) (Etempvar _t'6 tint) tint) (Val.of_bool isnew)).
  { eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; unfold le1; apply PTree.gss|].
    destruct isnew; reflexivity. }
  assert (HI1 : le1!_issuance = Some (Vptr bin (Ptrofs.repr ofs))).
  { unfold le1. rewrite PTree.gso by discriminate. exact HI. }
  destruct isnew.
  - destruct (eval_sha256_amount_repr Hmodel bx bm Hmx Hgx Hgm Hcx Hcm
      m l regs c ovf bin (ofs + 32) a HX ltac:(lia) Hix Him (HA eq_refl))
      as (mf & CF & XF & LF & PF & VF).
    exists mf. split.
    { rewrite eis_token_amount_shape. eapply exec_Sseq_1 with
        (t1 := E0) (t2 := E0) (le1 := eis_token_le le true bin ofs bz) (m1 := m).
      - unfold eis_token_choose_stmt. eapply exec_Sseq_1 with
          (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m); [exact ET|].
        eapply exec_Sifthenelse with (v1 := Val.of_bool true) (b := true);
          [exact EC|reflexivity|].
        apply exec_Sset. eapply eval_Ecast; [eapply eval_eis_token_addr; eassumption|reflexivity].
      - eapply exec_eis_conf_amount; [exact HG|exact HC|reflexivity| |exact CF].
        apply eval_Etempvar. unfold eis_token_le. apply PTree.gss. }
    split; [exact XF|]. split.
    { intros ch b o V _ Nx Nm. apply LF; assumption. }
    split; [exact PF|exact VF].
  - destruct (exec_eis_zero_init ___compound__2 e le1 m bz HZ HP)
      as (mi & CI & AZ & LI & PI & VI).
    assert (XI : ctxi mi bx bm l regs c ovf).
    { eapply ctxi_other; [exact HX| |].
      - intros ch b o HB. rewrite LI; [reflexivity|].
        left. destruct HB as [HB|[HB|[HB|HB]]]; congruence.
      - intros b o k p _ P. apply PI, P. }
    destruct (eval_sha256_amount_repr Hmodel bx bm Hmx Hgx Hgm Hcx Hcm
      mi l regs c ovf bz 0 (Explicit Int64.zero) XI
      ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) Hzx Hzm AZ)
      as (mf & CF & XF & LF & PF & VF).
    exists mf. split.
    { rewrite eis_token_amount_shape. eapply exec_Sseq_1 with
        (t1 := E0) (t2 := E0) (le1 := eis_token_le le false bin ofs bz) (m1 := mi).
      - unfold eis_token_choose_stmt. eapply exec_Sseq_1 with
          (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m); [exact ET|].
        eapply exec_Sifthenelse with (v1 := Val.of_bool false) (b := false);
          [exact EC|reflexivity|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mi);
          [exact CI|].
        apply exec_Sset. eapply eval_Ecast.
        + eapply eval_Eaddrof. apply eval_Evar_local; exact HZ.
        + reflexivity.
      - eapply exec_eis_conf_amount; [exact HG|exact HC|reflexivity| |exact CF].
        apply eval_Etempvar. unfold eis_token_le. apply PTree.gss. }
    split; [exact XF|]. split.
    { intros ch b o V Nz Nx Nm. rewrite LF by auto. apply LI; left; exact Nz. }
    split.
    { intros b o k p V P. apply PF; [auto|apply PI, P]. }
    intros b V. apply VF, VI, V.
Qed.
End Amounts.
