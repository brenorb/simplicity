(** Actual CurrentIndex wrapper. Physical field reads, source-copy entry and
    concrete writer call are separate from the canonical primitive consumer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_frame_layout C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_version_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge.
Set Default Timeout 10.

Lemma bitcoin_env_index_field :
  match (Clight.genv_cenv bitcoin_ge)!_txEnv with
  | Some co => field_offset (Clight.genv_cenv bitcoin_ge) _ix (co_members co) = OK (48, Full)
  | None => False end.
Proof. vm_compute; reflexivity. Qed.

Lemma eval_bitcoin_env_index e le m be base index :
  0 <= base -> base + 56 <= Ptrofs.max_unsigned ->
  le!_env = Some (Vptr be (Ptrofs.repr base)) ->
  Mem.load Mint64 m be (base + 48) = Some (Vlong index) ->
  eval_expr bitcoin_ge e le m
    (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr)))
      (Tstruct _txEnv noattr)) _ix tulong) (Vlong index).
Proof.
  intros HB HM HE HL. pose proof bitcoin_env_index_field as HField.
  destruct ((Clight.genv_cenv bitcoin_ge)!_txEnv) as [co|] eqn:HCo; [|contradiction].
  eapply eval_Elvalue.
  - eapply eval_Efield_struct with (co := co) (delta := 48).
    + eapply eval_Elvalue; [apply eval_Ederef, eval_Etempvar; exact HE|].
      apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HCo.
    + exact HField.
  - apply deref_loc_value with (chunk := Mint64); [reflexivity|].
    unfold Mem.loadv, Ptrofs.add. rewrite (Ptrofs.unsigned_repr base) by lia.
    change (Ptrofs.unsigned (Ptrofs.repr 48)) with 48.
    rewrite Ptrofs.unsigned_repr by lia; exact HL.
Qed.

Definition bitcoin_current_index_temps env bd dbase bs sbase : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps f_simplicity_bitcoin_current_index.(fn_temps)))).
Definition bitcoin_current_index_ready env bd dbase bs sbase index : temp_env :=
  PTree.set _t'1 (Vlong index) (bitcoin_current_index_temps env bd dbase bs sbase).

Lemma bitcoin_current_index_entry env m ma bl bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma,bl) ->
  function_entry2 bitcoin_ge f_simplicity_bitcoin_current_index
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
    m (bitcoin_version_locals bl) (bitcoin_current_index_temps env bd dbase bs sbase) ma.
Proof.
  intros HA. constructor.
  - change (list_norepet [_src]); repeat constructor; simpl; tauto.
  - change (list_norepet [_dst; _src; _env]); unfold _dst, _src, _env.
    repeat constructor; simpl; intuition discriminate.
  - change (list_disjoint [_dst; _src; _env] [_t'1]).
    intros i j HI HJ Heq; subst j; simpl in HI, HJ.
    destruct HI as [HI|[HI|[HI|HI]]]; destruct HJ as [HJ|HJ]; vm_compute in HI,HJ; congruence.
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma,bl)); exact HA.
    + constructor.
  - reflexivity.
Qed.

Lemma call_bitcoin_write32_arg e le m mf bd dbase arg value :
  typeof arg = tulong -> e!_simplicity_write32 = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  eval_expr bitcoin_ge e le m arg (Vlong value) ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_simplicity_write32)
    [Vptr bd (Ptrofs.repr dbase); Vlong value] E0 mf Vundef ->
  Clight2.exec_stmt bitcoin_ge e le m
    (Scall None (Evar _simplicity_write32
      (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr)); arg]) E0 le mf Out_normal.
Proof.
  intros HT HE HD HV HW.
  eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block _simplicity_write32) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vlong value])
    (f := Internal f_simplicity_write32) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [exact HE|exact bitcoin_write32_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs; [exact HV|rewrite HT; reflexivity|apply eval_Enil].
  - exact bitcoin_write32_funct.
  - reflexivity.
  - exact HW.
Qed.

Lemma eval_bitcoin_current_index_composes m ma mc me mf bl bd dbase bs sbase be ebase index bytes :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  Mem.alloc m 0 16 = (ma,bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Mem.load Mint64 mc be (ebase + 48) = Some (Vlong index) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal f_simplicity_write32)
    [Vptr bd (Ptrofs.repr dbase); Vlong index] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_simplicity_bitcoin_current_index)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vptr be (Ptrofs.repr ebase)]
    E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HE HM HA HL SC HIndex HW HF.
  set (env := Vptr be (Ptrofs.repr ebase)).
  set (le := bitcoin_current_index_temps env bd dbase bs sbase).
  set (ready := bitcoin_current_index_ready env bd dbase bs sbase index).
  eapply eval_funcall_internal with (e := bitcoin_version_locals bl) (le1 := le) (le2 := ready)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one,tint))).
  - apply bitcoin_current_index_entry; exact HA.
  - unfold f_simplicity_bitcoin_current_index; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_bitcoin_version_copy; [exact HB|exact HS|exact HD|reflexivity|exact HL|exact SC].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := ready).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := ready).
        -- apply exec_set. eapply eval_bitcoin_env_index; [exact HE|exact HM|reflexivity|exact HIndex].
        -- eapply call_bitcoin_write32_arg;
             [reflexivity|reflexivity|reflexivity|apply eval_Etempvar; reflexivity|exact HW].
      * apply exec_Sreturn_some, eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl,0,16)] = Some mf). cbn. rewrite HF; reflexivity.
Qed.
