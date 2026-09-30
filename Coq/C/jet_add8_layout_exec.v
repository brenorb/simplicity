(** Full add call composition with an arbitrary destination pointer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_add8 C.jet_increment8_exec.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition le_add8_layout_x env bd dofs bs sofs r :=
  PTree.set _x (Vint (add8_u r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env f_simplicity_add_8 bd dofs bs sofs)).
Definition le_add8_layout_ready env bd dofs bs sofs r s :=
  PTree.set _y (Vint (add8_u s)) (PTree.set _t'2 (Vint s)
    (le_add8_layout_x env bd dofs bs sofs r)).

Lemma eval_add8_layout_composes env m ma mc mr mr2 mb me mf bl bd dofs bs sbase bytes r s :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  ClightBigstep.Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8)
    [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  ClightBigstep.Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8)
    [Vptr bl Ptrofs.zero] E0 mr2 (Vint s) ->
  ClightBigstep.Clight2.eval_funcall ge0 mr2 (Internal f_writeBit)
    [Vptr bd dofs; Vint (add8_carry_bit r s)] E0 mb (Vint (add8_carry_bit r s)) ->
  ClightBigstep.Clight2.eval_funcall ge0 mb (Internal f_simplicity_write8)
    [Vptr bd dofs; Vint (add8_byte r s)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_add_8)
    [Vptr bd dofs; Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hread2 Hbit Hwrite HF.
  eapply ClightBigstep.eval_funcall_internal
    with (e := e_one8 bl)
      (le1 := le_arith8_layout env f_simplicity_add_8 bd dofs bs (Ptrofs.repr sbase))
      (le2 := le_add8_layout_ready env bd dofs bs (Ptrofs.repr sbase) r s)
      (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]).
    intros id1 id2 H1 H2 Heq. simpl in H1, H2. subst id2.
    destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - unfold f_simplicity_add_8; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_add8_layout_x env bd dofs bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- eapply call_add8_read; [apply symbol_read8|apply funct_read8|exact Hread].
        -- apply exec_set. eapply eval_Ecast.
           ++ eapply eval_Etempvar; reflexivity.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_add8_layout_ready env bd dofs bs (Ptrofs.repr sbase) r s).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - eapply call_add8_read; [apply symbol_read8|apply funct_read8|exact Hread2].
          - apply exec_set. eapply eval_Ecast.
            + eapply eval_Etempvar; reflexivity.
            + reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
        -- eapply call_frame_writer with (f := f_writeBit) (v := Vint (add8_carry_bit r s))
             (vret := Vint (add8_carry_bit r s)).
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_add8_carry_env; reflexivity.
           ++ apply cast_add8_carry.
           ++ exact Hbit.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
           ++ eapply call_frame_writer with (f := f_simplicity_write8) (v := Vint (add8_byte r s))
                (vret := Vundef).
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
              ** apply symbol_write8.
              ** apply funct_write8.
              ** apply eval_add8_sum_env; reflexivity.
              ** apply cast_add8_sum.
              ** exact Hwrite.
           ++ apply exec_Sreturn_some; apply eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf). cbn; rewrite HF; reflexivity.
Qed.
