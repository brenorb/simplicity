(** [simplicity_sha256_confAsset] and [simplicity_sha256_confNonce]
    (elements/ops.c): [simplicity_sha256_confidential] with the prefixes
    0x0a/0x0b (assets) and 0x02/0x03 (nonces). Reuses the archived
    [jet_elements_env_conf_wrap.v.source] call structure with [ctxi]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model.
Require Import C.jets_elements C.jet_elements_support_sha_linkage C.jet_elements_support_sha_add_n_init C.jet_elements_support_sha_be32_write C.jet_elements_support_sha_uchars_prep.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_support_sha_ctx_abs C.jet_elements_support_sha_uchars_exec C.jet_elements_confidential_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 20.

Lemma sha_confidential_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_sha256_confidential =
    Some (sha_symbol_block _simplicity_sha256_confidential).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_confidential_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _simplicity_sha256_confidential) Ptrofs.zero) =
    Some (Internal f_simplicity_sha256_confidential).
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Lemma eval_confAsset_call m m' (vctx vconf : val) :
  Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confidential)
    [Vint (Int.repr 10); Vint (Int.repr 11); vctx; vconf] E0 m' Vundef ->
  (exists b o, vctx = Vptr b o) -> (exists b o, vconf = Vptr b o) ->
  Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confAsset) [vctx; vconf] E0 m' Vundef.
Proof.
  intros HC (b1 & o1 & ->) (b2 & o2 & ->).
  set (le := PTree.set _asset (Vptr b2 o2) (PTree.set _ctx (Vptr b1 o1)
    (create_undef_temps (fn_temps f_simplicity_sha256_confAsset)))).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (m1 := m) (m2 := m') (le2 := le) (out := Out_normal).
  - apply function_entry2_intro.
    + apply list_norepet_nil.
    + repeat constructor; simpl; intuition discriminate.
    + intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
    + apply alloc_variables_nil.
    + reflexivity.
  - unfold f_simplicity_sha256_confAsset. cbn [fn_body].
    change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_sha256_confidential) Ptrofs.zero)
      (vargs := [Vint (Int.repr 10); Vint (Int.repr 11); Vptr b1 o1; Vptr b2 o2])
      (f := Internal f_simplicity_sha256_confidential).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_confidential_symbol]|].
      apply deref_loc_reference; reflexivity.
    + eapply eval_Econs; [apply eval_Econst_int|reflexivity|].
      eapply eval_Econs; [apply eval_Econst_int|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|apply eval_Enil].
    + exact sha_confidential_funct.
    + reflexivity.
    + exact HC.
  - reflexivity.
  - reflexivity.
Qed.

Lemma eval_confNonce_call m m' (vctx vconf : val) :
  Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confidential)
    [Vint (Int.repr 2); Vint (Int.repr 3); vctx; vconf] E0 m' Vundef ->
  (exists b o, vctx = Vptr b o) -> (exists b o, vconf = Vptr b o) ->
  Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confNonce) [vctx; vconf] E0 m' Vundef.
Proof.
  intros HC (b1 & o1 & ->) (b2 & o2 & ->).
  set (le := PTree.set _nonce (Vptr b2 o2) (PTree.set _ctx (Vptr b1 o1)
    (create_undef_temps (fn_temps f_simplicity_sha256_confNonce)))).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (m1 := m) (m2 := m') (le2 := le) (out := Out_normal).
  - apply function_entry2_intro.
    + apply list_norepet_nil.
    + repeat constructor; simpl; intuition discriminate.
    + intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
    + apply alloc_variables_nil.
    + reflexivity.
  - unfold f_simplicity_sha256_confNonce. cbn [fn_body].
    change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_sha256_confidential) Ptrofs.zero)
      (vargs := [Vint (Int.repr 2); Vint (Int.repr 3); Vptr b1 o1; Vptr b2 o2])
      (f := Internal f_simplicity_sha256_confidential).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_confidential_symbol]|].
      apply deref_loc_reference; reflexivity.
    + eapply eval_Econs; [apply eval_Econst_int|reflexivity|].
      eapply eval_Econs; [apply eval_Econst_int|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|apply eval_Enil].
    + exact sha_confidential_funct.
    + reflexivity.
    + exact HC.
  - reflexivity.
  - reflexivity.
Qed.

Section Wrap.
Variable Hmodel : memcpy_model.
Variables (bx bm : block) (l regs : list int) (c : int64) (ovf : bool).
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.
Variables (bc : block) (oc : Z) (ws : list int).
Hypothesis Hoc : 0 <= oc /\ oc + 36 <= Ptrofs.max_unsigned.
Hypothesis Hws : length ws = 8%nat.
Hypothesis Hbcx : bc <> bx.
Hypothesis Hbcm : bc <> bm.

Definition asset_bytes (pfx : int) : list int := conf_bytes (Int.repr 10) (Int.repr 11) pfx ws.
Definition nonce_bytes (pfx : int) : list int := conf_bytes (Int.repr 2) (Int.repr 3) pfx ws.

Theorem eval_sha256_confAsset m (pfx : int) :
  ctxi m bx bm l regs c ovf ->
  Mem.load Mint32 m bc (oc + 32) = Some (Vint pfx) ->
  pfx = Int.repr 0 \/ pfx = Int.repr 1 \/ pfx = Int.repr 2 \/ pfx = Int.repr 3 ->
  (pfx <> Int.repr 0 -> forall j, (j < 8)%nat -> Mem.load Mint32 m bc (oc + 4 * Z.of_nat j) = Some (Vint (nth j ws Int.zero))) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confAsset)
      [Vptr bx (Ptrofs.repr 0); Vptr bc (Ptrofs.repr oc)] E0 m' Vundef /\
    ctxi m' bx bm (fst (absorb_i l regs (asset_bytes pfx))) (snd (absorb_i l regs (asset_bytes pfx)))
      (Int64.add c (Int64.repr (Z.of_nat (length (asset_bytes pfx))))) (conf_overflow c ovf pfx) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k q, Mem.valid_block m b -> Mem.perm m b ofs k q -> Mem.perm m' b ofs k q) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HLS HP Hcase HW.
  destruct (eval_sha256_confidential Hmodel bx bm l regs c ovf Hmx Hgx Hgm Hcx Hcm bc oc
    (Int.repr 10) (Int.repr 11) ws Hoc eq_refl eq_refl Hws Hbcx Hbcm m pfx HLS HP Hcase HW)
    as (m' & HC & HL & FL & FP & FV).
  exists m'. split; [|split; [exact HL|split; [exact FL|split; [exact FP|exact FV]]]].
  apply eval_confAsset_call; [exact HC|eauto|eauto].
Qed.

Theorem eval_sha256_confNonce m (pfx : int) :
  ctxi m bx bm l regs c ovf ->
  Mem.load Mint32 m bc (oc + 32) = Some (Vint pfx) ->
  pfx = Int.repr 0 \/ pfx = Int.repr 1 \/ pfx = Int.repr 2 \/ pfx = Int.repr 3 ->
  (pfx <> Int.repr 0 -> forall j, (j < 8)%nat -> Mem.load Mint32 m bc (oc + 4 * Z.of_nat j) = Some (Vint (nth j ws Int.zero))) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confNonce)
      [Vptr bx (Ptrofs.repr 0); Vptr bc (Ptrofs.repr oc)] E0 m' Vundef /\
    ctxi m' bx bm (fst (absorb_i l regs (nonce_bytes pfx))) (snd (absorb_i l regs (nonce_bytes pfx)))
      (Int64.add c (Int64.repr (Z.of_nat (length (nonce_bytes pfx))))) (conf_overflow c ovf pfx) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k q, Mem.valid_block m b -> Mem.perm m b ofs k q -> Mem.perm m' b ofs k q) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HLS HP Hcase HW.
  destruct (eval_sha256_confidential Hmodel bx bm l regs c ovf Hmx Hgx Hgm Hcx Hcm bc oc
    (Int.repr 2) (Int.repr 3) ws Hoc eq_refl eq_refl Hws Hbcx Hbcm m pfx HLS HP Hcase HW)
    as (m' & HC & HL & FL & FP & FV).
  exists m'. split; [|split; [exact HL|split; [exact FL|split; [exact FP|exact FV]]]].
  apply eval_confNonce_call; [exact HC|eauto|eauto].
Qed.
End Wrap.
