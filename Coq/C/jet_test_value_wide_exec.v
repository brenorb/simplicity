(** Actual is_zero/is_one_16/32/64 bodies and their complete function boundaries. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_complement_wide_exec C.jet_readBit_layout C.jet_increment8_exec C.jet_test_value_spec.
Require Import C.jet_predicate_wide_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_test_value s (one : bool) := match s, one with
  | W16, false => f_simplicity_is_zero_16 | W32, false => f_simplicity_is_zero_32 | W64, false => f_simplicity_is_zero_64
  | W16, true => f_simplicity_is_one_16 | W32, true => f_simplicity_is_one_32 | W64, true => f_simplicity_is_one_64
  end.
Definition wide_test_value_expr (s : wide_size) (one : bool) :=
  Ebinop Oeq (Etempvar _x tulong) (Econst_int (if one then Int.one else Int.zero) tint) tint.
Definition wide_test_value_bit (s : wide_size) (one : bool) r :=
  Int64.eq r (if one then Int64.one else Int64.zero).
Definition le_wide_test_value_x env s one bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_test_value s one) bd dofs bs sofs)).

Lemma wide_test_value_body s one : (wide_test_value s one).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_complement_read s) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence (frame_writer_call _writeBit tbool tbool (wide_test_value_expr s one))
        (Sreturn (Some (Econst_int Int.one tint))))).
Proof. destruct s, one; reflexivity. Qed.

Lemma wide_test_value_denotes s one (x : Ty.tySem (Word (wide_log s))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  wide_test_value_bit s one r = Bit.toBool (@test_value_spec (wide_log s) one Alg.CoreFunSem x).
Proof.
  intros Hr. rewrite test_value_spec_numeric. unfold wide_test_value_bit, test_value_numeric.
  rewrite int64_eq_numeric, Hr. destruct one; reflexivity.
Qed.

Lemma eval_wide_test_value_expr s one e le m r :
  le!_x = Some (Vlong r) ->
  eval_expr ge0 e le m (wide_test_value_expr s one) (Vint (bit_int (wide_test_value_bit s one r))).
Proof.
  intros HX. destruct one, s; eapply eval_Ebinop.
  all: try (apply eval_Etempvar; exact HX).
  all: try apply eval_Econst_int.
  all: try apply eval_Econst_long.
  all: lazymatch goal with
    | |- _ = Some (Vint (bit_int ?b)) =>
        change (Some (Val.of_bool b) = Some (Vint (bit_int b)));
        destruct b; reflexivity
    end.
Qed.

Lemma eval_wide_test_value_composes env s one m ma mc mr me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (wide_test_value_bit s one r))] E0 me
    (Vint (bit_int (wide_test_value_bit s one r))) ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_test_value s one))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_test_value s one) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_test_value_x env s one bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s, one; reflexivity|destruct s, one; reflexivity| |exact HA].
    destruct s, one; change (list_disjoint [_dst; _src; _env] [_x; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_test_value_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s, one; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_complement_read. exact Hread.
        -- apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (bit_int (wide_test_value_bit s one r)))
             (v := Vint (bit_int (wide_test_value_bit s one r)))
             (vret := Vint (bit_int (wide_test_value_bit s one r))).
           ++ reflexivity.
           ++ unfold le_wide_test_value_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_wide_test_value_expr. unfold le_wide_test_value_x.
              rewrite PTree.gss. reflexivity.
           ++ destruct s, one; lazymatch goal with
                | |- _ = Some (Vint (bit_int ?b)) =>
                    change (sem_cast (Vint (bit_int b)) tint tbool mr = Some (Vint (bit_int b)));
                    destruct b; reflexivity
                end.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct s, one; cbn; split; solve [discriminate|reflexivity].
  - destruct s, one; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
