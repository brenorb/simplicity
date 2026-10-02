(** Actual zero-fill byte shift jet wrappers. The called helper is executed
    by the checked shared fill/count proof, rather than assumed as a result. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_readBit_layout.
Require Import C.jet_arith8_layout_exec C.jet_shift8_expr C.jet_shift8_helper_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift8_plain_function (right : bool) :=
  if right then f_simplicity_right_shift_8 else f_simplicity_left_shift_8.
Definition shift8_helper_id (right : bool) :=
  if right then _right_shift_helper_8 else _left_shift_helper_8.
Definition shift8_helper_call right := Scall None
  (Evar (shift8_helper_id right) (Tfunction
    (Tcons tbool (Tcons (tptr (Tstruct _frameItem noattr))
      (Tcons (tptr (Tstruct _frameItem noattr)) Tnil))) tvoid cc_default))
  [Econst_int Int.zero tint; Etempvar _dst (tptr (Tstruct _frameItem noattr));
    Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].

Lemma shift8_helper_symbol right : Genv.find_symbol (Clight.genv_genv ge0) (shift8_helper_id right) =
  Some (jet_symbol_block (shift8_helper_id right)).
Proof. destruct right; vm_compute; reflexivity. Qed.
Lemma shift8_helper_funct right : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block (shift8_helper_id right)) Ptrofs.zero) = Some (Internal (shift8_helper right)).
Proof. destruct right; vm_compute; reflexivity. Qed.

Lemma exec_shift8_helper_call right le m mf bl bd dofs a r mr mr2 :
  le!_dst = Some (Vptr bd dofs) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read4) [Vptr bl Ptrofs.zero] E0 mr (Vint a) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint r) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_write8)
    [Vptr bd dofs; Vint (Int.zero_ext 8 (shift8_payload right false r a))] E0 mf Vundef ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m (shift8_helper_call right) E0 le mf Out_normal.
Proof.
  intros HD HR4 HR8 HW.
  eapply exec_Scall with (vf := Vptr (jet_symbol_block (shift8_helper_id right)) Ptrofs.zero)
    (vargs := [Vint Int.zero; Vptr bd dofs; Vptr bl Ptrofs.zero])
    (f := Internal (shift8_helper right)) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [destruct right; reflexivity|apply shift8_helper_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + constructor.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Etempvar; exact HD.
      * reflexivity.
      * eapply eval_Econs.
        -- eapply eval_Eaddrof. eapply eval_Evar_local; reflexivity.
        -- reflexivity.
        -- apply eval_Enil.
  - apply shift8_helper_funct.
  - destruct right; reflexivity.
  - exact (@eval_shift8_helper_composes right false m mr mr2 mf bd dofs bl Ptrofs.zero a r HR4 HR8 HW).
Qed.

Lemma shift8_plain_body right : (shift8_plain_function right).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence (shift8_helper_call right) (Sreturn (Some (Econst_int Int.one tint)))).
Proof. destruct right; reflexivity. Qed.

Theorem eval_shift8_plain_composes env right m ma mc mr mr2 me mf bl bd dbase bs sbase bytes a r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read4) [Vptr bl Ptrofs.zero] E0 mr (Vint a) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint r) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (Int.zero_ext 8 (shift8_payload right false r a))] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (shift8_plain_function right))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC HR4 HR8 HW HF.
  set (le := le_arith8_layout env (shift8_plain_function right)
    bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  eapply eval_funcall_internal with (e := e_one8 bl) (le1 := le) (le2 := le)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct right; reflexivity|destruct right; reflexivity| |exact HA].
    destruct right; intros id1 id2 H1 H2 Heq; contradiction.
  - rewrite shift8_plain_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_frame_jet_copy; eauto.
      unfold le, le_arith8_layout; rewrite PTree.gso by discriminate; apply PTree.gss.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := le).
      * eapply exec_shift8_helper_call; [|exact HR4|exact HR8|exact HW].
        unfold le, le_arith8_layout; repeat rewrite PTree.gso by discriminate; apply PTree.gss.
      * apply exec_Sreturn_some; constructor.
  - destruct right; cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
