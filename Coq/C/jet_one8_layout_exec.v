(** The complete generated one_8 call with independent source/destination offsets. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition le_one8_layout env bd dbase bs sbase : temp_env :=
  PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
    (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
      (PTree.set _env env (PTree.empty val))).

Lemma entry_one8_layout env m ma bl bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) ->
  function_entry2 ge0 f_simplicity_one_8
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
    m (e_one8 bl) (le_one8_layout env bd dbase bs sbase) ma.
Proof.
  intros HA. constructor.
  - change (list_norepet [_src]). repeat constructor; simpl; tauto.
  - change (list_norepet [_dst; _src; _env]). unfold _dst, _src, _env.
    repeat constructor; simpl; intuition discriminate.
  - change (list_disjoint [_dst; _src; _env] []). intros x y Hx Hy; contradiction.
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + constructor.
  - reflexivity.
Qed.

Lemma call_one8_write_layout e le m mf bd dbase :
  e!_simplicity_write8 = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint Int.one] E0 mf Vundef ->
  ClightBigstep.Clight2.exec_stmt ge0 e le m
    (Scall None (Evar _simplicity_write8
      (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tuchar Tnil)) tvoid cc_default))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 1) tint])
    E0 le mf Out_normal.
Proof.
  intros HE HD HW.
  eapply exec_Scall with (vf := Vptr block_write8 Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vint Int.one])
    (f := Internal f_simplicity_write8) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [exact HE|apply symbol_write8].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Etempvar; exact HD.
    + reflexivity.
    + eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
  - apply funct_write8.
  - reflexivity.
  - exact HW.
Qed.

Lemma eval_one8_layout_composes env m ma mc me mf bl bd dbase bs sbase bytes :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  ClightBigstep.Clight2.eval_funcall ge0 mc (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint Int.one] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_one_8)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HSbase HSAlign HD HA HB SC HW HF.
  assert (HS : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HSbase; lia. }
  eapply ClightBigstep.eval_funcall_internal
    with (e := e_one8 bl) (le1 := le_one8_layout env bd dbase bs sbase)
      (le2 := le_one8_layout env bd dbase bs sbase) (m1 := ma) (m2 := me)
      (out := Out_return (Some (Vint Int.one, tint))).
  - apply entry_one8_layout; exact HA.
  - unfold f_simplicity_one_8; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_Sassign_copy.
      * eapply eval_Evar_local; reflexivity.
      * eapply eval_Etempvar; reflexivity.
      * reflexivity.
      * eapply assign_frameItem_copy.
        -- reflexivity.
        -- intros _. rewrite HS; exact HSAlign.
        -- intros _. exists 0; reflexivity.
        -- left; exact HD.
        -- rewrite HS; exact HB.
        -- exact SC.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply call_one8_write_layout; [reflexivity|reflexivity|exact HW].
      * apply exec_Sreturn_some; apply eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf). cbn. rewrite HF; reflexivity.
Qed.
