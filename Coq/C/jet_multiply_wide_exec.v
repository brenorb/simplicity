(** Actual multiply_16/32 bodies: two narrow reads, one doubled-width write.
    This INTERNAL composition contract is discharged by initial-only layouts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_binary_wide_exec C.jet_multiply_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Inductive multiply_wide_size := M16 | M32.
Definition multiply_input_size s := match s with M16 => W16 | M32 => W32 end.
Definition multiply_output_size s := match s with M16 => W32 | M32 => W64 end.
Definition wide_multiply s := match s with
  M16 => f_simplicity_multiply_16 | M32 => f_simplicity_multiply_32 end.
Definition wide_multiply_expr :=
  Ebinop Omul (Etempvar _x tulong) (Etempvar _y tulong) tulong.
Definition wide_multiply_spec s {term : Alg.Core.Algebra} :
    @Alg.Core.domain term
      (Ty.Prod (Word.Word (wide_log (multiply_input_size s)))
        (Word.Word (wide_log (multiply_input_size s))))
      (Word.Word (wide_log (multiply_output_size s))) :=
  match s with
  | M16 => @multiply_word_spec 4 term
  | M32 => @multiply_word_spec 5 term
  end.
Definition le_wide_multiply_x env s bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_multiply s) bd dofs bs sofs)).
Definition le_wide_multiply_y env s bd dofs bs sofs r t :=
  PTree.set _y (Vlong t) (PTree.set _t'2 (Vlong t) (le_wide_multiply_x env s bd dofs bs sofs r)).

Lemma wide_multiply_body s : (wide_multiply s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read (multiply_input_size s) _t'1) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence (wide_binary_read (multiply_input_size s) _t'2) (Sset _y (Etempvar _t'2 tulong)))
        (Ssequence (frame_writer_call (wide_writer_id (multiply_output_size s)) tulong tvoid (wide_multiply_expr))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct s; reflexivity. Qed.

Lemma eval_wide_multiply_expr e le m r t :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  eval_expr ge0 e le m (wide_multiply_expr) (Vlong (Int64.mul r t)).
Proof.
  intros HX HY. eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vlong t).
  - eapply eval_Etempvar; exact HX.
  - eapply eval_Etempvar; exact HY.
  - reflexivity.
Qed.

Lemma eval_wide_multiply_composes env s m ma mc mr mr2 me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader (multiply_input_size s))) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader (multiply_input_size s))) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong t) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_writer (multiply_output_size s)))
    [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.mul r t)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_multiply s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_multiply s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_multiply_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s; change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_multiply_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_multiply_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_binary_read. exact Hread1.
        -- apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_wide_binary_read. exact Hread2.
          - apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := wide_writer (multiply_output_size s))
             (vraw := Vlong (Int64.mul r t)) (v := Vlong (Int64.mul r t)) (vret := Vundef).
           ++ destruct s; reflexivity.
           ++ unfold le_wide_multiply_y, le_wide_multiply_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ destruct s; reflexivity.
           ++ apply wide_writer_symbol.
           ++ apply wide_writer_funct.
           ++ apply eval_wide_multiply_expr.
              ** unfold le_wide_multiply_y, le_wide_multiply_x.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** unfold le_wide_multiply_y. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - destruct s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
