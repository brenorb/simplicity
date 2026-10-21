(** Execute an issuance ID compound literal and absorb it, rather than assume
    a preinitialized confidential object. Shared by the actual asset/token
    prefixes of issuance_hash. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_read8s_layout.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_elements_prim C.jet_elements_asset_jets C.jet_elements_conf_hash_repr.
Require Import C.jet_elements_asset_amount_hash_spec C.jet_elements_conf_hash_bridge.
Require Import C.jet_elements_input_utxo_prep C.jet_elements_input_utxo_payload.
Require Import C.jet_elements_field_eval.
Require Import C.jet_elements_issuance_asset_literal C.jet_elements_single_issuance_prep.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_support_sha_uchars_prep.
Require Import C.jet_elements_confidential_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.
Local Notation CONF := (Tstruct _confidential noattr).
Local Notation ISS := (Tstruct _assetIssuance noattr).

Definition eis_conf_asset_stmt (id : ident) : statement :=
  Scall None (Evar _simplicity_sha256_confAsset
    (Tfunction (Tcons CTXP (Tcons (tptr CONF) Tnil)) tvoid cc_default))
    [Eaddrof (Evar _ctx CTX) CTXP; Eaddrof (Evar id CONF) (tptr CONF)].

Definition eis_asset_prefix : statement :=
  ltac:(let s := eval cbv delta [eis_some] beta iota in eis_some in
    lazymatch s with Ssequence ?first _ => exact first end).
Definition eis_token_prefix : statement :=
  ltac:(let s := eval cbv delta [eis_some] beta iota in eis_some in
    lazymatch s with Ssequence _ (Ssequence _ (Ssequence ?third _)) => exact third end).

Lemma eis_asset_prefix_shape : eis_asset_prefix =
  Ssequence eis_asset_init_actual (eis_conf_asset_stmt ___compound).
Proof. reflexivity. Qed.
Lemma eis_token_prefix_shape : eis_token_prefix =
  Ssequence eis_token_init_actual (eis_conf_asset_stmt ___compound__1).
Proof. reflexivity. Qed.

Lemma exec_eis_conf_asset e le m mf id bx ba :
  e!_simplicity_sha256_confAsset = None -> e!_ctx = Some (bx, CTX) ->
  e!id = Some (ba, CONF) ->
  Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confAsset)
    [Vptr bx Ptrofs.zero; Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt sha_ge e le m (eis_conf_asset_stmt id) E0 le mf Out_normal.
Proof.
  intros HG HC HA HCall. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_sha256_confAsset) Ptrofs.zero)
    (vargs := [Vptr bx Ptrofs.zero; Vptr ba Ptrofs.zero]) (f := Internal f_simplicity_sha256_confAsset).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact HG|exact eiu_conf_asset_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact HC|reflexivity|].
    eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact HA|reflexivity|apply eval_Enil].
  - exact eiu_conf_asset_funct.
  - reflexivity.
  - exact HCall.
Qed.

Section LiteralHash.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem exec_eis_literal_asset_hash e le m id source ba bin base h l regs c ovf :
  ctxi m bx bm l regs c ovf ->
  e!id = Some (ba, CONF) -> e!_ctx = Some (bx, CTX) ->
  e!_simplicity_sha256_confAsset = None ->
  typeof source = MID -> eval_expr sha_ge e le m source (Vptr bin (Ptrofs.repr base)) ->
  ba <> bin -> ba <> bx -> ba <> bm -> ba <> GC -> ba <> GM ->
  0 <= base -> base + 32 <= Ptrofs.max_unsigned ->
  uint32_array_at m bin base (hash256_reg h) ->
  Mem.range_perm m ba 0 36 Cur Writable ->
  let B := map word8_array_value (elements_asset_bytes (encode_asset (Explicit h : assetWith unit))) in
  exists mf,
    Clight2.exec_stmt sha_ge e le m
      (Ssequence (eis_asset_literal_stmt id source) (eis_conf_asset_stmt id)) E0 le mf Out_normal /\
    ctxi mf bx bm (fst (absorb_i l regs B)) (snd (absorb_i l regs B))
      (Int64.add c (Int64.repr 33)) (conf_overflow c ovf Int.one) /\
    (forall ch b o, Mem.valid_block m b -> b <> ba -> b <> bx -> b <> bm ->
      Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HX HE HC HG HS HSource Hbi Hbx Hbm Hbg Hbc HO HM HW HP B.
  destruct (exec_eis_asset_literal e le m id source ba bin base h HE HS HSource Hbi HO HM HW HP)
    as (mi & CI & HA & LI & PI & VI).
  assert (XI : ctxi mi bx bm l regs c ovf).
  { eapply ctxi_other; [exact HX| |].
    - intros ch b o HB. rewrite LI; [reflexivity|].
      left. destruct HB as [HB|[HB|[HB|HB]]]; congruence.
    - intros b o k p _ P. apply PI, P. }
  destruct (eval_sha256_asset_repr Hmodel bx bm Hmx Hgx Hgm Hcx Hcm mi l regs c ovf ba 0
    (Explicit h) XI ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) Hbx Hbm HA)
    as (mf & CF & XF & LF & PF & VF).
  fold B in XF. assert (HL : length B = 33%nat) by apply eiu_asset_len.
  rewrite HL in XF.
  exists mf. split.
  { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mi); [exact CI|].
    eapply exec_eis_conf_asset; eassumption. }
  split; [exact XF|]. split.
  { intros ch b o V Na Nx Nm. rewrite LF by auto. apply LI; left; exact Na. }
  split.
  { intros b o k p V P. apply PF; [auto|apply PI, P]. }
  intros b V. apply VF, VI, V.
Qed.
End LiteralHash.

Lemma eis_asset_id_offset : elements_field_at _assetIssuance _assetId 168.
Proof. vm_compute; reflexivity. Qed.
Lemma eis_token_id_offset : elements_field_at _assetIssuance _tokenId 200.
Proof. vm_compute; reflexivity. Qed.

(** Instantiate the literal+serializer proof at either real C subtree. The
    source expression is derived from _issuance; its execution is not a
    precondition of this contract. *)
Theorem exec_eis_id_hash (Hmodel : memcpy_model) bx bm (token : bool) e le m ba bin ofs h l regs c ovf :
  bm <> bx -> GC <> bx -> GC <> bm -> GM <> bx -> GM <> bm ->
  ctxi m bx bm l regs c ovf ->
  e!(if token then ___compound__1 else ___compound) = Some (ba, CONF) ->
  e!_ctx = Some (bx, CTX) -> e!_simplicity_sha256_confAsset = None ->
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  ba <> bin -> ba <> bx -> ba <> bm -> ba <> GC -> ba <> GM ->
  0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned ->
  uint32_array_at m bin (ofs + if token then 200 else 168) (hash256_reg h) ->
  Mem.range_perm m ba 0 36 Cur Writable ->
  let B := map word8_array_value (elements_asset_bytes (encode_asset (Explicit h : assetWith unit))) in
  exists mf,
    Clight2.exec_stmt sha_ge e le m
      (if token then eis_token_prefix else eis_asset_prefix) E0 le mf Out_normal /\
    ctxi mf bx bm (fst (absorb_i l regs B)) (snd (absorb_i l regs B))
      (Int64.add c (Int64.repr 33)) (conf_overflow c ovf Int.one) /\
    (forall ch b o, Mem.valid_block m b -> b <> ba -> b <> bx -> b <> bm ->
      Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros Hmx Hgx Hgm Hcx Hcm HX HE HC HG HI Hbi Hbx Hbm Hbg Hbc HO HM HW HP B.
  set (field := if token then _tokenId else _assetId).
  set (delta := if token then 200 else 168).
  assert (HF : elements_field_at _assetIssuance field delta).
  { unfold field, delta. destruct token; [exact eis_token_id_offset|exact eis_asset_id_offset]. }
  assert (HS : eval_expr sha_ge e le m
    (Efield (Ederef (Etempvar _issuance (tptr ISS)) ISS) field MID)
    (Vptr bin (Ptrofs.repr (ofs + delta)))).
  { rewrite <- (elements_ptr_add_repr ofs delta) by (unfold delta; destruct token; lia).
    eapply eval_elements_field_struct; [reflexivity|exact HF|].
    apply eval_elements_deref_struct. exact HI. }
  destruct (exec_eis_literal_asset_hash Hmodel bx bm Hmx Hgx Hgm Hcx Hcm
    e le m (if token then ___compound__1 else ___compound)
    (Efield (Ederef (Etempvar _issuance (tptr ISS)) ISS) field MID)
    ba bin (ofs + delta) h l regs c ovf HX HE HC HG eq_refl HS Hbi Hbx Hbm Hbg Hbc
    ltac:(unfold delta; destruct token; lia) ltac:(unfold delta; destruct token; lia) HW HP)
    as (mf & CE & XF & LF & PF & VF).
  exists mf. split.
  { unfold field in CE. destruct token; [rewrite eis_token_prefix_shape, eis_token_literal_shape|
      rewrite eis_asset_prefix_shape, eis_asset_literal_shape]; exact CE. }
  split; [exact XF|]. split; [exact LF|]. split; [exact PF|exact VF].
Qed.
