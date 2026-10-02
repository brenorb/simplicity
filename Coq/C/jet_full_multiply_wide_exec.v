(** Actual full_multiply_16/32 bodies, plus their shared long expression.
    INTERNAL composition lemmas: final layout contracts derive all calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_frame_layout.
Require Import C.jet_arith8_layout_exec C.jet_wide C.jet_binary_wide_exec.
Require Import C.jet_multiply_wide_exec C.jet_full_multiply_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition full_multiply_value r t u v := Int64.add (Int64.add (Int64.mul r t) u) v.
Definition full_multiply_expr := Ebinop Oadd
  (Ebinop Oadd (Ebinop Omul (Etempvar _x tulong) (Etempvar _y tulong) tulong)
    (Etempvar _z tulong) tulong) (Etempvar _w tulong) tulong.
Definition wide_full_multiply s := match s with
  M16 => f_simplicity_full_multiply_16 | M32 => f_simplicity_full_multiply_32 end.
Definition wide_full_multiply_spec s {term : Alg.Core.Algebra} :
    @Alg.Core.domain term
      (Ty.Prod
        (Ty.Prod (Word (wide_log (multiply_input_size s))) (Word (wide_log (multiply_input_size s))))
        (Ty.Prod (Word (wide_log (multiply_input_size s))) (Word (wide_log (multiply_input_size s)))))
      (Word (wide_log (multiply_output_size s))) :=
  match s with M16 => @fullMultiplier 4 term | M32 => @fullMultiplier 5 term end.
Definition le_wide_full_multiply_x env s bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_full_multiply s) bd dofs bs sofs)).
Definition le_wide_full_multiply_y env s bd dofs bs sofs r t :=
  PTree.set _y (Vlong t) (PTree.set _t'2 (Vlong t)
    (le_wide_full_multiply_x env s bd dofs bs sofs r)).
Definition le_wide_full_multiply_z env s bd dofs bs sofs r t u :=
  PTree.set _z (Vlong u) (PTree.set _t'3 (Vlong u)
    (le_wide_full_multiply_y env s bd dofs bs sofs r t)).
Definition le_wide_full_multiply_w env s bd dofs bs sofs r t u v :=
  PTree.set _w (Vlong v) (PTree.set _t'4 (Vlong v)
    (le_wide_full_multiply_z env s bd dofs bs sofs r t u)).

Lemma wide_full_multiply_body s : (wide_full_multiply s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read (multiply_input_size s) _t'1) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence (wide_binary_read (multiply_input_size s) _t'2) (Sset _y (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence (wide_binary_read (multiply_input_size s) _t'3) (Sset _z (Etempvar _t'3 tulong)))
          (Ssequence
            (Ssequence (wide_binary_read (multiply_input_size s) _t'4) (Sset _w (Etempvar _t'4 tulong)))
            (Ssequence (frame_writer_call (wide_writer_id (multiply_output_size s)) tulong tvoid full_multiply_expr)
              (Sreturn (Some (Econst_int Int.one tint)))))))).
Proof. destruct s; reflexivity. Qed.

Lemma eval_full_multiply_expr e le m r t u v :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  le!_z = Some (Vlong u) -> le!_w = Some (Vlong v) ->
  eval_expr ge0 e le m full_multiply_expr (Vlong (full_multiply_value r t u v)).
Proof.
  intros HX HY HZ HW.
  eapply eval_Ebinop with (v1 := Vlong (Int64.add (Int64.mul r t) u)) (v2 := Vlong v).
  - eapply eval_Ebinop with (v1 := Vlong (Int64.mul r t)) (v2 := Vlong u).
    + eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vlong t).
      * apply eval_Etempvar; exact HX.
      * apply eval_Etempvar; exact HY.
      * reflexivity.
    + apply eval_Etempvar; exact HZ.
    + reflexivity.
  - apply eval_Etempvar; exact HW.
  - reflexivity.
Qed.

Lemma eval_wide_full_multiply_composes env s m ma mc mr mr2 mr3 mr4 me mf bl bd dbase bs sbase bytes r t u v :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader (multiply_input_size s))) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader (multiply_input_size s))) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong t) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_reader (multiply_input_size s))) [Vptr bl Ptrofs.zero] E0 mr3 (Vlong u) ->
  Clight2.eval_funcall ge0 mr3 (Internal (wide_reader (multiply_input_size s))) [Vptr bl Ptrofs.zero] E0 mr4 (Vlong v) ->
  Clight2.eval_funcall ge0 mr4 (Internal (wide_writer (multiply_output_size s)))
    [Vptr bd (Ptrofs.repr dbase); Vlong (full_multiply_value r t u v)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_full_multiply s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hread3 Hread4 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_full_multiply s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_full_multiply_w env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u v)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s; change (list_disjoint [_dst; _src; _env] [_x; _y; _z; _w; _t'4; _t'3; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]];
      destruct H2 as [H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|H2]]]]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_full_multiply_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_full_multiply_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        - apply call_wide_binary_read; exact Hread1.
        - apply exec_set. apply eval_Etempvar. rewrite PTree.gss; reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
        (le1 := le_wide_full_multiply_y env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        - apply call_wide_binary_read; exact Hread2.
        - apply exec_set. apply eval_Etempvar. rewrite PTree.gss; reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3)
        (le1 := le_wide_full_multiply_z env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
        - apply call_wide_binary_read; exact Hread3.
        - apply exec_set. apply eval_Etempvar. rewrite PTree.gss; reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr4)
        (le1 := le_wide_full_multiply_w env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u v).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr4).
        - apply call_wide_binary_read; exact Hread4.
        - apply exec_set. apply eval_Etempvar. rewrite PTree.gss; reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
      * eapply call_frame_writer_cast with (f := wide_writer (multiply_output_size s))
          (vraw := Vlong (full_multiply_value r t u v)) (v := Vlong (full_multiply_value r t u v)) (vret := Vundef).
        -- destruct s; reflexivity.
        -- unfold le_wide_full_multiply_w, le_wide_full_multiply_z, le_wide_full_multiply_y,
             le_wide_full_multiply_x, le_arith8_layout.
           rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
        -- destruct s; reflexivity.
        -- apply wide_writer_symbol.
        -- apply wide_writer_funct.
        -- apply eval_full_multiply_expr;
             unfold le_wide_full_multiply_w, le_wide_full_multiply_z, le_wide_full_multiply_y,
               le_wide_full_multiply_x;
             rewrite ?PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
        -- reflexivity.
        -- exact Hwrite.
      * apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - destruct s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
