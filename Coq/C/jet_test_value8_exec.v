(** Actual byte is_zero/is_one comparisons, promotions and complete C calls. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_read8.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec C.jet_increment8_exec.
Require Import C.jet_add8_word C.jet_binary8_exec C.jet_readBit_layout C.jet_test_value_spec.
Require Import C.jet_predicate8_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition test_value8 (one : bool) := if one then f_simplicity_is_one_8 else f_simplicity_is_zero_8.
Definition test_value8_expr (one : bool) :=
  Ebinop Oeq (Etempvar _x tuchar) (Econst_int (if one then Int.one else Int.zero) tint) tint.
Definition test_value8_bit (one : bool) r :=
  Int.eq (Int.zero_ext 8 r) (if one then Int.one else Int.zero).
Definition le_test_value8_x env one bd dofs bs sofs r :=
  PTree.set _x (Vint (Int.zero_ext 8 r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env (test_value8 one) bd dofs bs sofs)).

Lemma test_value8_denotes one payload :
  test_value8_bit one (read8_result payload) =
    Bit.toBool (@test_value_spec 3 one Alg.CoreFunSem (decode_word8 payload)).
Proof.
  rewrite test_value_spec_numeric. unfold test_value8_bit, test_value_numeric.
  rewrite int_eq_numeric, read8_result_unsigned. destruct one; reflexivity.
Qed.

Lemma test_value8_body one : (test_value8 one).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence (frame_writer_call _writeBit tbool tbool (test_value8_expr one))
        (Sreturn (Some (Econst_int Int.one tint))))).
Proof. destruct one; reflexivity. Qed.

Lemma eval_test_value8_expr one e le m r :
  le!_x = Some (Vint (Int.zero_ext 8 r)) ->
  eval_expr ge0 e le m (test_value8_expr one) (Vint (bit_int (test_value8_bit one r))).
Proof.
  intros HX. destruct one; eapply eval_Ebinop.
  all: try (apply eval_Etempvar; exact HX).
  all: try apply eval_Econst_int.
  all: lazymatch goal with
    | |- _ = Some (Vint (bit_int ?b)) =>
        change (Some (Val.of_bool b) = Some (Vint (bit_int b))); destruct b; reflexivity
    end.
Qed.

Lemma eval_test_value8_composes env one m ma mc mr me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (test_value8_bit one r))] E0 me
    (Vint (bit_int (test_value8_bit one r))) ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (test_value8 one))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (test_value8 one) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_test_value8_x env one bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct one; reflexivity|destruct one; reflexivity| |exact HA].
    destruct one; change (list_disjoint [_dst; _src; _env] [_x; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite test_value8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct one; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary8_read. exact Hread.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint r).
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (bit_int (test_value8_bit one r)))
             (v := Vint (bit_int (test_value8_bit one r)))
             (vret := Vint (bit_int (test_value8_bit one r))).
           ++ reflexivity.
           ++ unfold le_test_value8_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_test_value8_expr. unfold le_test_value8_x. rewrite PTree.gss. reflexivity.
           ++ destruct one; lazymatch goal with
                | |- _ = Some (Vint (bit_int ?b)) =>
                    change (sem_cast (Vint (bit_int b)) tint tbool mr = Some (Vint (bit_int b)));
                    destruct b; reflexivity
                end.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct one; cbn; split; solve [discriminate|reflexivity].
  - destruct one; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
