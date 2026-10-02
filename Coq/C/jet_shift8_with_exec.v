(** Actual fill-input byte shift wrappers: source copy, Boolean read/cast,
    both helper branches, byte write, return and local frame free. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_readBit_layout.
Require Import C.jet_arith8_layout_exec C.jet_complement1_exec.
Require Import C.jet_shift8_expr C.jet_shift8_helper_exec C.jet_shift8_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift8_with_function (right : bool) :=
  if right then f_simplicity_right_shift_with_8 else f_simplicity_left_shift_with_8.
Definition shift8_with_helper_call right := Scall None
  (Evar (shift8_helper_id right) (Tfunction
    (Tcons tbool (Tcons (tptr (Tstruct _frameItem noattr))
      (Tcons (tptr (Tstruct _frameItem noattr)) Tnil))) tvoid cc_default))
  [Etempvar _with tbool; Etempvar _dst (tptr (Tstruct _frameItem noattr));
    Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Definition le_shift8_with env right bd dofs bs sofs fill :=
  PTree.set _with (Vint (bit_int fill)) (PTree.set _t'1 (Vint (bit_int fill))
    (le_arith8_layout env (shift8_with_function right) bd dofs bs sofs)).

Lemma exec_shift8_with_helper_call right fill le m mf bl bd dofs a r mr mr2 :
  le!_dst = Some (Vptr bd dofs) -> le!_with = Some (Vint (bit_int fill)) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read4) [Vptr bl Ptrofs.zero] E0 mr (Vint a) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint r) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_write8)
    [Vptr bd dofs; Vint (Int.zero_ext 8 (shift8_payload right fill r a))] E0 mf Vundef ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m (shift8_with_helper_call right) E0 le mf Out_normal.
Proof.
  intros HD HF HR4 HR8 HW.
  eapply exec_Scall with (vf := Vptr (jet_symbol_block (shift8_helper_id right)) Ptrofs.zero)
    (vargs := [Vint (bit_int fill); Vptr bd dofs; Vptr bl Ptrofs.zero])
    (f := Internal (shift8_helper right)) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [destruct right; reflexivity|apply shift8_helper_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HF.
    + destruct fill; reflexivity.
    + eapply eval_Econs.
      * apply eval_Etempvar; exact HD.
      * reflexivity.
      * eapply eval_Econs.
        -- eapply eval_Eaddrof. eapply eval_Evar_local; reflexivity.
        -- reflexivity.
        -- apply eval_Enil.
  - apply shift8_helper_funct.
  - destruct right; reflexivity.
  - exact (@eval_shift8_helper_composes right fill m mr mr2 mf bd dofs bl Ptrofs.zero a r HR4 HR8 HW).
Qed.

Lemma shift8_with_body right : (shift8_with_function right).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence bit_jet_read (Sset _with (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence (shift8_with_helper_call right) (Sreturn (Some (Econst_int Int.one tint))))).
Proof. destruct right; reflexivity. Qed.

Theorem eval_shift8_with_composes env right fill m ma mc mb mr mr2 me mf bl bd dbase bs sbase bytes a r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mb (Vint (bit_int fill)) ->
  Clight2.eval_funcall ge0 mb (Internal f_simplicity_read4) [Vptr bl Ptrofs.zero] E0 mr (Vint a) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint r) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (Int.zero_ext 8 (shift8_payload right fill r a))] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (shift8_with_function right))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC HBit HR4 HR8 HW HF.
  set (le := le_arith8_layout env (shift8_with_function right)
    bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  set (lef := le_shift8_with env right bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) fill).
  eapply eval_funcall_internal with (e := e_one8 bl) (le1 := le) (le2 := lef)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct right; reflexivity|destruct right; reflexivity| |exact HA].
    replace (map fst (fn_temps (shift8_with_function right))) with [_with; _t'1]
      by (destruct right; reflexivity).
    intros id1 id2 H1 H2 Heq. cbn in H1, H2. subst id2.
    destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite shift8_with_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_frame_jet_copy; eauto.
      unfold le, le_arith8_layout; rewrite PTree.gso by discriminate; apply PTree.gss.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := lef).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
        -- apply call_bit_jet_read; exact HBit.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int fill)).
           ++ apply eval_Etempvar; apply PTree.gss.
           ++ destruct fill; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lef).
        -- eapply exec_shift8_with_helper_call; [| |exact HR4|exact HR8|exact HW].
           ++ unfold lef, le_shift8_with, le_arith8_layout.
              repeat rewrite PTree.gso by discriminate; apply PTree.gss.
           ++ unfold lef, le_shift8_with; apply PTree.gss.
        -- apply exec_Sreturn_some; constructor.
  - destruct right; cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
