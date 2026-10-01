(** Shared actual-body execution for complement_16/32/64. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_complement s := match s with
  W16 => f_simplicity_complement_16 | W32 => f_simplicity_complement_32 | W64 => f_simplicity_complement_64 end.
Definition wide_complement_read s :=
  Scall (Some _t'1)
    (Evar (wide_reader_id s) (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tulong cc_default))
    [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Definition wide_complement_expr :=
  Eunop Onotint (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tulong) tulong) tulong.
Definition le_wide_complement_x env s bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_complement s) bd dofs bs sofs)).

Lemma wide_complement_body s : (wide_complement s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_complement_read s) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence (frame_writer_call (wide_writer_id s) tulong tvoid wide_complement_expr)
        (Sreturn (Some (Econst_int Int.one tint))))).
Proof. destruct s; reflexivity. Qed.

Lemma call_wide_complement_read s le m mr bl r :
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal (wide_reader s))
    [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  ClightBigstep.Clight2.exec_stmt ge0 (e_one8 bl) le m (wide_complement_read s)
    E0 (PTree.set _t'1 (Vlong r) le) mr Out_normal.
Proof.
  intros Hread.
  eapply exec_Scall with (vf := Vptr (jet_symbol_block (wide_reader_id s)) Ptrofs.zero)
    (vargs := [Vptr bl Ptrofs.zero]) (f := Internal (wide_reader s)) (vres := Vlong r).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [destruct s; reflexivity|apply wide_reader_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Eaddrof. eapply eval_Evar_local. reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - apply wide_reader_funct.
  - destruct s; reflexivity.
  - exact Hread.
Qed.

Lemma eval_wide_complement_expr m e le r :
  le!_x = Some (Vlong r) -> eval_expr ge0 e le m wide_complement_expr (Vlong (Int64.not r)).
Proof.
  intros HX. unfold wide_complement_expr.
  eapply eval_Eunop with (v1 := Vlong r).
  - eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong r).
    + apply eval_Econst_int.
    + eapply eval_Etempvar; exact HX.
    + change (Some (Vlong (Int64.mul Int64.one r)) = Some (Vlong r)).
      rewrite Int64.mul_commut, Int64.mul_one. reflexivity.
  - reflexivity.
Qed.

Lemma eval_wide_complement_composes env s m ma mc mr me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  ClightBigstep.Clight2.eval_funcall ge0 mc (Internal (wide_reader s))
    [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  ClightBigstep.Clight2.eval_funcall ge0 mr (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.not r)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal (wide_complement s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hwrite HF.
  eapply ClightBigstep.eval_funcall_internal
    with (e := e_one8 bl)
      (le1 := le_arith8_layout env (wide_complement s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
      (le2 := le_wide_complement_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)
      (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s; change (list_disjoint [_dst; _src; _env] [_x; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_complement_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_complement_read. exact Hread.
        -- apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := wide_writer s)
             (vraw := Vlong (Int64.not r)) (v := Vlong (Int64.not r)) (vret := Vundef).
           ++ destruct s; reflexivity.
           ++ unfold le_wide_complement_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ destruct s; reflexivity.
           ++ apply wide_writer_symbol.
           ++ apply wide_writer_funct.
           ++ apply eval_wide_complement_expr. unfold le_wide_complement_x.
              rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct s; cbn; split; solve [discriminate | reflexivity].
  - destruct s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
