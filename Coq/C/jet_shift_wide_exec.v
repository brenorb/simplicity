(** Actual zero-fill LP64 wide shift jet wrappers. The called helper is executed
    by the checked shared fill/count proof, rather than assumed as a result. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_readBit_layout.
Require Import C.jet_arith8_layout_exec C.jet_wide C.jet_shift8_helper_exec C.jet_shift_wide_expr C.jet_shift_wide_helper_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift_wide_plain_function s (right : bool) := match s, right with
  | W16, false => f_simplicity_left_shift_16 | W16, true => f_simplicity_right_shift_16
  | W32, false => f_simplicity_left_shift_32 | W32, true => f_simplicity_right_shift_32
  | W64, false => f_simplicity_left_shift_64 | W64, true => f_simplicity_right_shift_64 end.
Definition shift_wide_helper_id s (right : bool) := match s, right with
  | W16, false => _left_shift_helper_16 | W16, true => _right_shift_helper_16
  | W32, false => _left_shift_helper_32 | W32, true => _right_shift_helper_32
  | W64, false => _left_shift_helper_64 | W64, true => _right_shift_helper_64 end.
Definition shift_wide_helper_call s right := Scall None
  (Evar (shift_wide_helper_id s right) (Tfunction
    (Tcons tbool (Tcons (tptr (Tstruct _frameItem noattr))
      (Tcons (tptr (Tstruct _frameItem noattr)) Tnil))) tvoid cc_default))
  [Econst_int Int.zero tint; Etempvar _dst (tptr (Tstruct _frameItem noattr));
    Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].

Lemma shift_wide_helper_symbol s right : Genv.find_symbol (Clight.genv_genv ge0) (shift_wide_helper_id s right) =
  Some (jet_symbol_block (shift_wide_helper_id s right)).
Proof. destruct s, right; vm_compute; reflexivity. Qed.
Lemma shift_wide_helper_funct s right : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block (shift_wide_helper_id s right)) Ptrofs.zero) = Some (Internal (shift_wide_helper s right)).
Proof. destruct s, right; vm_compute; reflexivity. Qed.

Lemma exec_shift_wide_helper_call s right le m mf bl bd dofs a r mr mr2 :
  le!_dst = Some (Vptr bd dofs) ->
  Clight2.eval_funcall ge0 m (Internal (shift8_reader_function (match s with W16 => true | _ => false end))) [Vptr bl Ptrofs.zero] E0 mr (Vint a) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong r) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_writer s))
    [Vptr bd dofs; Vlong (shift_wide_payload s right false r a)] E0 mf Vundef ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m (shift_wide_helper_call s right) E0 le mf Out_normal.
Proof.
  intros HD HR4 HR8 HW.
  eapply exec_Scall with (vf := Vptr (jet_symbol_block (shift_wide_helper_id s right)) Ptrofs.zero)
    (vargs := [Vint Int.zero; Vptr bd dofs; Vptr bl Ptrofs.zero])
    (f := Internal (shift_wide_helper s right)) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [destruct s, right; reflexivity|apply shift_wide_helper_symbol].
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
  - apply shift_wide_helper_funct.
  - destruct s, right; reflexivity.
  - exact (@eval_shift_wide_helper_composes s right false m mr mr2 mf bd dofs bl Ptrofs.zero a r HR4 HR8 HW).
Qed.

Lemma shift_wide_plain_body s right : (shift_wide_plain_function s right).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence (shift_wide_helper_call s right) (Sreturn (Some (Econst_int Int.one tint)))).
Proof. destruct s, right; reflexivity. Qed.

Theorem eval_shift_wide_plain_composes env s right m ma mc mr mr2 me mf bl bd dbase bs sbase bytes a r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (shift8_reader_function (match s with W16 => true | _ => false end))) [Vptr bl Ptrofs.zero] E0 mr (Vint a) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong r) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (shift_wide_payload s right false r a)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (shift_wide_plain_function s right))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC HR4 HR8 HW HF.
  set (le := le_arith8_layout env (shift_wide_plain_function s right)
    bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  eapply eval_funcall_internal with (e := e_one8 bl) (le1 := le) (le2 := le)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s, right; reflexivity|destruct s, right; reflexivity| |exact HA].
    destruct s, right; intros id1 id2 H1 H2 Heq; contradiction.
  - rewrite shift_wide_plain_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_frame_jet_copy; eauto.
      unfold le, le_arith8_layout; rewrite PTree.gso by discriminate; apply PTree.gss.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := le).
      * eapply exec_shift_wide_helper_call; [|exact HR4|exact HR8|exact HW].
        unfold le, le_arith8_layout; repeat rewrite PTree.gso by discriminate; apply PTree.gss.
      * apply exec_Sreturn_some; constructor.
  - destruct s, right; cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
