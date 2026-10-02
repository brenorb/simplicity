(** Actual parse_lock body and function boundary. The threshold's uint-to-long
    promotion and the Boolean argument cast are kept in the Clight derivation. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout.
Require Import C.jet_arith8_layout_exec C.jet_increment8_exec C.jet_increment32_layout_exec.
Require Import C.jet_wide C.jet_timelock_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition parse_lock_tag_expr := Ebinop Ole (Econst_int (Int.repr 500000000) tuint)
  (Etempvar _nLockTime tulong) tint.
Definition le_parse_lock_x env bd dofs bs sofs r :=
  PTree.set _nLockTime (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env f_simplicity_parse_lock bd dofs bs sofs)).

Lemma eval_parse_lock_tag e le m r :
  le!_nLockTime = Some (Vlong r) ->
  eval_expr ge0 e le m parse_lock_tag_expr
    (Vint (if parse_lock_tag r then Int.one else Int.zero)).
Proof.
  intros HX. unfold parse_lock_tag_expr.
  eapply eval_Ebinop with (v1 := Vint (Int.repr 500000000)) (v2 := Vlong r).
  - apply eval_Econst_int.
  - apply eval_Etempvar; exact HX.
  - change (Some (Val.of_bool (negb (Int64.ltu r (Int64.repr 500000000)))) =
      Some (Vint (if parse_lock_tag r then Int.one else Int.zero))).
    unfold parse_lock_tag. destruct (Int64.ltu r (Int64.repr 500000000)); reflexivity.
Qed.

Lemma cast_parse_lock_tag m r :
  sem_cast (Vint (if parse_lock_tag r then Int.one else Int.zero))
    (typeof parse_lock_tag_expr) tbool m =
    Some (Vint (if parse_lock_tag r then Int.one else Int.zero)).
Proof. unfold parse_lock_tag. destruct (Int64.ltu r (Int64.repr 500000000)); reflexivity. Qed.

Lemma eval_parse_lock_composes env m ma mc mr mb me mf bl bd dofs bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read32) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal f_writeBit)
    [Vptr bd dofs; Vint (if parse_lock_tag r then Int.one else Int.zero)] E0 mb
      (Vint (if parse_lock_tag r then Int.one else Int.zero)) ->
  Clight2.eval_funcall ge0 mb (Internal (wide_writer W32)) [Vptr bd dofs; Vlong r] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_parse_lock)
    [Vptr bd dofs; Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hbit Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_parse_lock bd dofs bs (Ptrofs.repr sbase))
    (le2 := le_parse_lock_x env bd dofs bs (Ptrofs.repr sbase) r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_nLockTime; _t'1]).
    intros id1 id2 H1 H2 Heq. cbn in H1, H2. subst id2.
    destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - unfold f_simplicity_parse_lock; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- eapply call_increment32_read; [apply symbol_read32|apply funct_read32|exact Hread].
        -- apply exec_set. eapply eval_Etempvar; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (if parse_lock_tag r then Int.one else Int.zero))
             (v := Vint (if parse_lock_tag r then Int.one else Int.zero))
             (vret := Vint (if parse_lock_tag r then Int.one else Int.zero)).
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_parse_lock_tag. reflexivity.
           ++ apply cast_parse_lock_tag.
           ++ exact Hbit.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
           ++ eapply call_frame_writer_cast with (f := wide_writer W32)
                (b := jet_symbol_block (wide_writer_id W32))
                (vraw := Vlong r) (v := Vlong r) (vret := Vundef).
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
              ** exact (wide_writer_symbol W32).
              ** exact (wide_writer_funct W32).
              ** apply eval_Etempvar; reflexivity.
              ** reflexivity.
              ** exact Hwrite.
           ++ apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf). cbn; rewrite HF; reflexivity.
Qed.
