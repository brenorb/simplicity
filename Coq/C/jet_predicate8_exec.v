(** Actual byte some/all comparisons, promotions and complete C calls. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_read8.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec C.jet_increment8_exec.
Require Import C.jet_add8_word C.jet_binary8_exec C.jet_readBit_layout C.jet_predicate_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition predicate8 (all : bool) := if all then f_simplicity_all_8 else f_simplicity_some_8.
Definition predicate8_expr (all : bool) :=
  if all then Ebinop Oeq (Etempvar _x tuchar) (Econst_int (Int.repr 255) tint) tint
  else Ebinop One (Etempvar _x tuchar) (Econst_int Int.zero tint) tint.
Definition predicate8_bit (all : bool) r :=
  if all then Int.eq (Int.zero_ext 8 r) (Int.repr 255) else negb (Int.eq (Int.zero_ext 8 r) Int.zero).
Definition le_predicate8_x env all bd dofs bs sofs r :=
  PTree.set _x (Vint (Int.zero_ext 8 r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env (predicate8 all) bd dofs bs sofs)).

Lemma int_eq_numeric r t : Int.eq r t = Z.eqb (Int.unsigned r) (Int.unsigned t).
Proof.
  unfold Int.eq. destruct (zeq (Int.unsigned r) (Int.unsigned t)); symmetry;
    [apply Z.eqb_eq|apply Z.eqb_neq]; assumption.
Qed.
Lemma predicate8_denotes all payload :
  predicate8_bit all (read8_result payload) =
    Bit.toBool (@predicate_spec 3 all Alg.CoreFunSem (decode_word8 payload)).
Proof.
  rewrite predicate_spec_numeric. unfold predicate8_bit. destruct all.
  - rewrite int_eq_numeric, read8_result_unsigned.
    change (Z.eqb (@toZ (WordToZ 3) (decode_word8 payload)) 255 =
      Z.eqb (@toZ (WordToZ 3) (decode_word8 payload)) 255). reflexivity.
  - rewrite int_eq_numeric, Int.unsigned_zero, read8_result_unsigned. reflexivity.
Qed.

Lemma predicate8_body all : (predicate8 all).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence (frame_writer_call _writeBit tbool tbool (predicate8_expr all))
        (Sreturn (Some (Econst_int Int.one tint))))).
Proof. destruct all; reflexivity. Qed.

Lemma eval_predicate8_expr all e le m r :
  le!_x = Some (Vint (Int.zero_ext 8 r)) ->
  eval_expr ge0 e le m (predicate8_expr all) (Vint (bit_int (predicate8_bit all r))).
Proof.
  intros HX. destruct all; eapply eval_Ebinop.
  all: try (apply eval_Etempvar; exact HX).
  all: try apply eval_Econst_int.
  all: lazymatch goal with
    | |- _ = Some (Vint (bit_int ?b)) =>
        change (Some (Val.of_bool b) = Some (Vint (bit_int b))); destruct b; reflexivity
    end.
Qed.

Lemma eval_predicate8_composes env all m ma mc mr me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (predicate8_bit all r))] E0 me
    (Vint (bit_int (predicate8_bit all r))) ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (predicate8 all))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (predicate8 all) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_predicate8_x env all bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct all; reflexivity|destruct all; reflexivity| |exact HA].
    destruct all; change (list_disjoint [_dst; _src; _env] [_x; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite predicate8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct all; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary8_read. exact Hread.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint r).
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (bit_int (predicate8_bit all r)))
             (v := Vint (bit_int (predicate8_bit all r)))
             (vret := Vint (bit_int (predicate8_bit all r))).
           ++ reflexivity.
           ++ unfold le_predicate8_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_predicate8_expr. unfold le_predicate8_x. rewrite PTree.gss. reflexivity.
           ++ destruct all; lazymatch goal with
                | |- _ = Some (Vint (bit_int ?b)) =>
                    change (sem_cast (Vint (bit_int b)) tint tbool mr = Some (Vint (bit_int b)));
                    destruct b; reflexivity
                end.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct all; cbn; split; solve [discriminate|reflexivity].
  - destruct all; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
