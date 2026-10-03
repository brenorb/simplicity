(** Actual Bitcoin version wrapper: entry, by-value source copy, environment
    field reads, concrete write32 call and local cleanup. Composition is internal;
    the initial-memory consumer must derive allocation/copy/write/free premises. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_frame_layout C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_env_read.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge.
Set Default Timeout 10.

Definition bitcoin_version_locals bl : env :=
  PTree.set _src (bl, Tstruct _frameItem noattr) empty_env.
Definition bitcoin_version_temps env bd dbase bs sbase : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps f_simplicity_bitcoin_version.(fn_temps)))).
Definition bitcoin_version_ready env bd dbase bs sbase bt txbase version : temp_env :=
  PTree.set _t'2 (Vlong version) (PTree.set _t'1 (Vptr bt (Ptrofs.repr txbase))
    (bitcoin_version_temps env bd dbase bs sbase)).

Lemma bitcoin_version_entry env m ma bl bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) ->
  function_entry2 bitcoin_ge f_simplicity_bitcoin_version
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
    m (bitcoin_version_locals bl) (bitcoin_version_temps env bd dbase bs sbase) ma.
Proof.
  intros HA. constructor.
  - change (list_norepet [_src]). repeat constructor; simpl; tauto.
  - change (list_norepet [_dst; _src; _env]); unfold _dst, _src, _env.
    repeat constructor; simpl; intuition discriminate.
  - change (list_disjoint [_dst; _src; _env] [_t'2; _t'1]).
    intros i j HI HJ Heq; subst j; simpl in HI, HJ.
    destruct HI as [HI|[HI|[HI|HI]]];
      destruct HJ as [HJ|[HJ|HJ]]; vm_compute in HI, HJ; congruence.
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma,bl)); exact HA.
    + constructor.
  - reflexivity.
Qed.

Lemma exec_bitcoin_version_copy m mc bl bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) le m
    (Sassign (Evar _src (Tstruct _frameItem noattr))
      (Etempvar _src (Tstruct _frameItem noattr))) E0 le mc Out_normal.
Proof.
  intros HB HS HD HL Hload Hstore.
  assert (HA : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HB; lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local; reflexivity.
  - apply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
    + reflexivity.
    + intros _. change (8 | Ptrofs.unsigned (Ptrofs.repr sbase)). rewrite HA; exact HS.
    + intros _. change (8 | 0); exists 0; reflexivity.
    + left; congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes).
      rewrite HA; exact Hload.
    + exact Hstore.
Qed.

Lemma call_bitcoin_version_write32 e le m mf bd dbase version :
  e!_simplicity_write32 = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_t'2 = Some (Vlong version) ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_simplicity_write32)
    [Vptr bd (Ptrofs.repr dbase); Vlong version] E0 mf Vundef ->
  Clight2.exec_stmt bitcoin_ge e le m
    (Scall None (Evar _simplicity_write32
      (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'2 tulong])
    E0 le mf Out_normal.
Proof.
  intros HE HD HV HW.
  eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block _simplicity_write32) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vlong version])
    (f := Internal f_simplicity_write32) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [exact HE|exact bitcoin_write32_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact HV|reflexivity|apply eval_Enil].
  - exact bitcoin_write32_funct.
  - reflexivity.
  - exact HW.
Qed.

Lemma eval_bitcoin_version_composes m ma mc me mf bl bd dbase bs sbase be ebase bt txbase version bytes :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  0 <= ebase <= Ptrofs.max_unsigned -> 0 <= txbase -> txbase + 488 <= Ptrofs.max_unsigned ->
  Mem.alloc m 0 16 = (ma,bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Mem.load Mptr mc be ebase = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mint64 mc bt (txbase + 464) = Some (Vlong version) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal f_simplicity_write32)
    [Vptr bd (Ptrofs.repr dbase); Vlong version] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_simplicity_bitcoin_version)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vptr be (Ptrofs.repr ebase)]
    E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HE HT HTMax HA HL SC HEnv HVersion HW HF.
  set (env := Vptr be (Ptrofs.repr ebase)).
  set (le := bitcoin_version_temps env bd dbase bs sbase).
  set (letx := PTree.set _t'1 (Vptr bt (Ptrofs.repr txbase)) le).
  set (ready := bitcoin_version_ready env bd dbase bs sbase bt txbase version).
  eapply eval_funcall_internal with (e := bitcoin_version_locals bl) (le1 := le) (le2 := ready)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - apply bitcoin_version_entry; exact HA.
  - unfold f_simplicity_bitcoin_version; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_bitcoin_version_copy; [exact HB|exact HS|exact HD|reflexivity|exact HL|exact SC].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := ready).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := letx).
        -- apply exec_set. eapply eval_bitcoin_env_tx; [exact HE|reflexivity|exact HEnv].
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := ready).
           ++ apply exec_set. eapply eval_bitcoin_tx_version; [exact HT|exact HTMax|reflexivity|exact HVersion].
           ++ eapply call_bitcoin_version_write32; [reflexivity|reflexivity|reflexivity|exact HW].
      * apply exec_Sreturn_some, eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl,0,16)] = Some mf). cbn. rewrite HF; reflexivity.
Qed.
