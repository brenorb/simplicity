(** [sha_256_ctx_8_add_n]: environment, entry, and the four calls of its
    body (context reader, read8s, sha256_uchars, context writer). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_read8s_layout C.jet_uint32_array_init.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_uchars_prep C.jet_sha_add_n_init.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Lemma an_read_context_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_read_sha256_context =
    Some (sha_symbol_block _simplicity_read_sha256_context).
Proof. vm_compute; reflexivity. Qed.
Lemma an_read_context_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _simplicity_read_sha256_context) Ptrofs.zero) =
    Some (Internal jets.f_simplicity_read_sha256_context).
Proof. vm_compute; reflexivity. Qed.
Lemma an_read8s_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _read8s = Some (sha_symbol_block _read8s).
Proof. vm_compute; reflexivity. Qed.
Lemma an_read8s_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _read8s) Ptrofs.zero) =
    Some (Internal jets.f_read8s).
Proof. vm_compute; reflexivity. Qed.
Lemma an_uchars_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_uchars = Some (sha_symbol_block _sha256_uchars).
Proof. vm_compute; reflexivity. Qed.
Lemma an_uchars_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero) =
    Some (Internal f_sha256_uchars).
Proof. vm_compute; reflexivity. Qed.
Lemma an_write_context_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_write_sha256_context =
    Some (sha_symbol_block _simplicity_write_sha256_context).
Proof. vm_compute; reflexivity. Qed.
Lemma an_write_context_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _simplicity_write_sha256_context) Ptrofs.zero) =
    Some (Internal jets.f_simplicity_write_sha256_context).
Proof. vm_compute; reflexivity. Qed.

Definition an_env (bm bb bx : block) : env :=
  PTree.set _ctx (bx, CTX) (PTree.set _buf (bb, tarray tuchar 512) (PTree.set _midstate (bm, MID) empty_env)).

Definition an_temps (bd : block) (dbase : Z) (bsf : block) (sbase : Z) (vn : int64) : temp_env :=
  PTree.set _n (Vlong vn) (PTree.set _src (Vptr bsf (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase)) (create_undef_temps (fn_temps f_sha_256_ctx_8_add_n)))).

Lemma an_blocks bm bb bx :
  blocks_of_env sha_ge (an_env bm bb bx) = [(bx, 0, 88); (bm, 0, 32); (bb, 0, 512)].
Proof. vm_compute. reflexivity. Qed.

Lemma an_entry m m1 m2 m3 bm bb bx bd dbase bsf sbase vn :
  Mem.alloc m 0 32 = (m1, bm) -> Mem.alloc m1 0 512 = (m2, bb) -> Mem.alloc m2 0 88 = (m3, bx) ->
  function_entry2 sha_ge f_sha_256_ctx_8_add_n
    [Vptr bd (Ptrofs.repr dbase); Vptr bsf (Ptrofs.repr sbase); Vlong vn] m
    (an_env bm bb bx) (an_temps bd dbase bsf sbase vn) m3.
Proof.
  intros HA HB HC. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bm).
    + change (Mem.alloc m 0 32 = (m1, bm)); exact HA.
    + eapply alloc_variables_cons with (m1 := m2) (b1 := bb).
      * change (Mem.alloc m1 0 512 = (m2, bb)); exact HB.
      * eapply alloc_variables_cons with (m1 := m3) (b1 := bx).
        -- change (Mem.alloc m2 0 88 = (m3, bx)); exact HC.
        -- constructor.
  - reflexivity.
Qed.

Local Opaque sha_ge.

Section Calls.
Variables (bm bb bx : block).
Let e := an_env bm bb bx.

Lemma an_eval_ctx_addr le m :
  eval_expr sha_ge e le m (Eaddrof (Evar _ctx CTX) CTXP) (Vptr bx Ptrofs.zero).
Proof. eapply eval_Eaddrof. apply eval_Evar_local. reflexivity. Qed.

Lemma an_eval_buf le m :
  eval_expr sha_ge e le m (Evar _buf (tarray tuchar 512)) (Vptr bb Ptrofs.zero).
Proof.
  eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
Qed.

Lemma an_call_read le m m' bsf sbase v :
  le!_src = Some (Vptr bsf (Ptrofs.repr sbase)) ->
  Clight2.eval_funcall sha_ge m (Internal jets.f_simplicity_read_sha256_context)
    [Vptr bx Ptrofs.zero; Vptr bsf (Ptrofs.repr sbase)] E0 m' v ->
  Clight2.exec_stmt sha_ge e le m
    (Scall (Some _t'3) (Evar _simplicity_read_sha256_context
        (Tfunction (Tcons CTXP (Tcons FRP Tnil)) tbool cc_default))
      [Eaddrof (Evar _ctx CTX) CTXP; Etempvar _src FRP])
    E0 (PTree.set _t'3 v le) m' Out_normal.
Proof.
  intros HS HC. change (PTree.set _t'3 v le) with (set_opttemp (Some _t'3) v le).
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_read_sha256_context) Ptrofs.zero)
    (vargs := [Vptr bx Ptrofs.zero; Vptr bsf (Ptrofs.repr sbase)]).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact an_read_context_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply an_eval_ctx_addr|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact HS|reflexivity|apply eval_Enil].
  - exact an_read_context_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma an_call_read8s le m m' bsf sbase vn :
  le!_src = Some (Vptr bsf (Ptrofs.repr sbase)) -> le!_n = Some (Vlong vn) ->
  Clight2.eval_funcall sha_ge m (Internal jets.f_read8s)
    [Vptr bb Ptrofs.zero; Vlong vn; Vptr bsf (Ptrofs.repr sbase)] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m an_read8s E0 le m' Out_normal.
Proof.
  intros HS HN HC. change le with (set_opttemp None Vundef le) at 2. unfold an_read8s.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _read8s) Ptrofs.zero)
    (vargs := [Vptr bb Ptrofs.zero; Vlong vn; Vptr bsf (Ptrofs.repr sbase)]).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact an_read8s_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply an_eval_buf|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact HN|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact HS|reflexivity|apply eval_Enil].
  - exact an_read8s_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma an_call_uchars le m m' vn v :
  le!_n = Some (Vlong vn) ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_uchars)
    [Vptr bx Ptrofs.zero; Vptr bb Ptrofs.zero; Vlong vn] E0 m' v ->
  Clight2.exec_stmt sha_ge e le m an_uchars E0 le m' Out_normal.
Proof.
  intros HN HC. change le with (set_opttemp None v le) at 2. unfold an_uchars.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
    (vargs := [Vptr bx Ptrofs.zero; Vptr bb Ptrofs.zero; Vlong vn]).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact an_uchars_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply an_eval_ctx_addr|reflexivity|].
    eapply eval_Econs; [apply an_eval_buf|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact HN|reflexivity|apply eval_Enil].
  - exact an_uchars_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma an_call_write le m m' bd dbase v :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall sha_ge m (Internal jets.f_simplicity_write_sha256_context)
    [Vptr bd (Ptrofs.repr dbase); Vptr bx Ptrofs.zero] E0 m' v ->
  Clight2.exec_stmt sha_ge e le m
    (Scall (Some _t'4) (Evar _simplicity_write_sha256_context
        (Tfunction (Tcons FRP (Tcons CTXP Tnil)) tbool cc_default))
      [Etempvar _dst FRP; Eaddrof (Evar _ctx CTX) CTXP])
    E0 (PTree.set _t'4 v le) m' Out_normal.
Proof.
  intros HD HC. change (PTree.set _t'4 v le) with (set_opttemp (Some _t'4) v le).
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_write_sha256_context) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bx Ptrofs.zero]).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact an_write_context_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs; [apply an_eval_ctx_addr|reflexivity|apply eval_Enil].
  - exact an_write_context_funct.
  - reflexivity.
  - exact HC.
Qed.
End Calls.

(** ** Array predicates in indexed form *)
Lemma u8_nth m b base xs :
  uint8_array_at m b base xs -> forall i, (i < length xs)%nat ->
  Mem.load Mint8unsigned m b (base + Z.of_nat i) = Some (Vint (nth i xs Int.zero)).
Proof. intros H i Hi. apply H. apply nth_error_nth'. exact Hi. Qed.

Lemma u8_of_nth m b base xs :
  (forall i, (i < length xs)%nat ->
     Mem.load Mint8unsigned m b (base + Z.of_nat i) = Some (Vint (nth i xs Int.zero))) ->
  uint8_array_at m b base xs.
Proof.
  intros H i x Hi.
  assert (HL : (i < length xs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  rewrite (H i HL). rewrite (nth_error_nth _ _ Int.zero Hi). reflexivity.
Qed.

Lemma u32_nth m b base xs :
  uint32_array_at m b base xs -> forall i, (i < length xs)%nat ->
  Mem.load Mint32 m b (base + 4 * Z.of_nat i) = Some (Vint (nth i xs Int.zero)).
Proof. intros H i Hi. apply H. apply nth_error_nth'. exact Hi. Qed.

Lemma u32_of_nth m b base xs :
  (forall i, (i < length xs)%nat ->
     Mem.load Mint32 m b (base + 4 * Z.of_nat i) = Some (Vint (nth i xs Int.zero))) ->
  uint32_array_at m b base xs.
Proof.
  intros H i x Hi.
  assert (HL : (i < length xs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  rewrite (H i HL). rewrite (nth_error_nth _ _ Int.zero Hi). reflexivity.
Qed.
