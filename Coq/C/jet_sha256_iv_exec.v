(** Actual two-local SHA256 IV jet lifecycle. Intermediate calls here are
    discharged from initial permissions by jet_sha256_iv_layout. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition sha256_iv_jet_env bl biv :=
  PTree.set _iv (biv, tarray tuint 8) (e_one8 bl).
Definition sha256_iv_jet_temps env bd dbase bs sbase :=
  le_arith8_layout env f_simplicity_sha_256_iv bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase).

Lemma sha256_iv_jet_entry env m ma mb bl biv bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 32 = (mb, biv) ->
  function_entry2 ge0 f_simplicity_sha_256_iv
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
    m (sha256_iv_jet_env bl biv) (sha256_iv_jet_temps env bd dbase bs sbase) mb.
Proof.
  intros HA HB. constructor.
  - change (list_norepet [_src; _iv]). unfold _src, _iv.
    repeat constructor; simpl; intuition discriminate.
  - change (list_norepet [_dst; _src; _env]). unfold _dst, _src, _env.
    repeat constructor; simpl; intuition discriminate.
  - change (list_disjoint [_dst; _src; _env] []). intros i j HI HJ; contradiction.
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := biv).
      * change (Mem.alloc ma 0 32 = (mb, biv)); exact HB.
      * constructor.
  - reflexivity.
Qed.

Lemma exec_sha256_iv_source_copy m mc bl biv bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt ge0 (sha256_iv_jet_env bl biv) le m
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    E0 le mc Out_normal.
Proof.
  intros HB HS HD HL Hload Hstore.
  assert (HA : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HB; lia. }
  eapply exec_Sassign_copy.
  - eapply eval_Evar_local; reflexivity.
  - eapply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_frameItem_copy.
    + reflexivity.
    + intros _. rewrite HA; exact HS.
    + intros _. exists 0; reflexivity.
    + left; exact HD.
    + rewrite HA; exact Hload.
    + exact Hstore.
Qed.

Lemma sha256_iv_symbol : Genv.find_symbol (Clight.genv_genv ge0) _sha256_iv =
  Some (jet_symbol_block _sha256_iv).
Proof. vm_compute; reflexivity. Qed.
Lemma sha256_iv_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _sha256_iv) Ptrofs.zero) = Some (Internal f_sha256_iv).
Proof. vm_compute; reflexivity. Qed.
Lemma write32s_symbol : Genv.find_symbol (Clight.genv_genv ge0) _write32s =
  Some (jet_symbol_block _write32s).
Proof. vm_compute; reflexivity. Qed.
Lemma write32s_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _write32s) Ptrofs.zero) = Some (Internal f_write32s).
Proof. vm_compute; reflexivity. Qed.

Lemma call_sha256_iv_init m mf bl biv le :
  Clight2.eval_funcall ge0 m (Internal f_sha256_iv) [Vptr biv Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt ge0 (sha256_iv_jet_env bl biv) le m
    (Scall None (Evar _sha256_iv (Tfunction (Tcons (tptr tuint) Tnil) tvoid cc_default))
      [Evar _iv (tarray tuint 8)]) E0 le mf Out_normal.
Proof.
  intros Hcall. eapply exec_Scall with (vf := Vptr (jet_symbol_block _sha256_iv) Ptrofs.zero)
    (vargs := [Vptr biv Ptrofs.zero]) (f := Internal f_sha256_iv) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|apply sha256_iv_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Elvalue; [eapply eval_Evar_local; reflexivity|].
      apply deref_loc_reference; reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - apply sha256_iv_funct.
  - reflexivity.
  - exact Hcall.
Qed.

Lemma call_sha256_iv_write32s m mf bl biv le bd dbase :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall ge0 m (Internal f_write32s)
    [Vptr bd (Ptrofs.repr dbase); Vptr biv Ptrofs.zero; Vlong (Int64.repr 8)] E0 mf Vundef ->
  Clight2.exec_stmt ge0 (sha256_iv_jet_env bl biv) le m
    (Scall None (Evar _write32s (Tfunction
      (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr tuint) (Tcons tulong Tnil)))
        tvoid cc_default))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Evar _iv (tarray tuint 8);
        Econst_int (Int.repr 8) tint]) E0 le mf Out_normal.
Proof.
  intros HD Hcall. eapply exec_Scall with (vf := Vptr (jet_symbol_block _write32s) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr biv Ptrofs.zero; Vlong (Int64.repr 8)])
    (f := Internal f_write32s) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|apply write32s_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs.
    + eapply eval_Elvalue; [eapply eval_Evar_local; reflexivity|].
      apply deref_loc_reference; reflexivity.
    + reflexivity.
    + eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
  - apply write32s_funct.
  - reflexivity.
  - exact Hcall.
Qed.

Lemma eval_sha256_iv_composes env m ma mb mc mi me mt mf bl biv bd dbase bs sbase bytes :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 32 = (mb, biv) ->
  Mem.loadbytes mb bs sbase 16 = Some bytes -> Mem.storebytes mb bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_sha256_iv) [Vptr biv Ptrofs.zero] E0 mi Vundef ->
  Clight2.eval_funcall ge0 mi (Internal f_write32s)
    [Vptr bd (Ptrofs.repr dbase); Vptr biv Ptrofs.zero; Vlong (Int64.repr 8)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mt -> Mem.free mt biv 0 32 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_sha_256_iv)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HS HA HD HallocS HallocIV Hbytes Hstore Hinit Hwrite HfreeS HfreeIV.
  set (le := sha256_iv_jet_temps env bd dbase bs sbase).
  eapply eval_funcall_internal with (e := sha256_iv_jet_env bl biv)
    (le1 := le) (le2 := le) (m1 := mb) (m2 := me)
    (out := Out_return (Some (Vint Int.one, tint))).
  - eapply sha256_iv_jet_entry; eauto.
  - change (Clight2.exec_stmt ge0 (sha256_iv_jet_env bl biv) le mb
      f_simplicity_sha_256_iv.(fn_body) E0 le me (Out_return (Some (Vint Int.one, tint)))).
    cbn [fn_body]. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_sha256_iv_source_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi).
      * apply call_sha256_iv_init; exact Hinit.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- eapply call_sha256_iv_write32s; [reflexivity|exact Hwrite].
        -- apply exec_Sreturn_some; apply eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16); (biv, 0, 32)] = Some mf).
    cbn. rewrite HfreeS, HfreeIV; reflexivity.
Qed.
