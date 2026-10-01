(** Actual some/all_16/32/64 bodies and their complete function boundaries. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_complement_wide_exec C.jet_readBit_layout C.jet_increment8_exec C.jet_predicate_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_predicate s (all : bool) := match s, all with
  | W16, false => f_simplicity_some_16 | W32, false => f_simplicity_some_32 | W64, false => f_simplicity_some_64
  | W16, true => f_simplicity_all_16 | W32, true => f_simplicity_all_32 | W64, true => f_simplicity_all_64
  end.
Definition wide_predicate_expr s (all : bool) :=
  if all then Ebinop Oeq (Etempvar _x tulong)
    (match s with
     | W16 => Econst_int (Int.repr 65535) tint
     | W32 => Econst_int (Int.repr (-1)) tuint
     | W64 => Econst_long (Int64.repr (-1)) tulong end) tint
  else Ebinop One (Etempvar _x tulong) (Econst_int Int.zero tint) tint.
Definition wide_predicate_bit s (all : bool) r :=
  if all then Int64.eq r (Int64.repr (word_modulus (wide_log s) - 1))
  else negb (Int64.eq r Int64.zero).
Definition le_wide_predicate_x env s all bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_predicate s all) bd dofs bs sofs)).

Lemma wide_predicate_body s all : (wide_predicate s all).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_complement_read s) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence (frame_writer_call _writeBit tbool tbool (wide_predicate_expr s all))
        (Sreturn (Some (Econst_int Int.one tint))))).
Proof. destruct s, all; reflexivity. Qed.

Lemma int64_eq_numeric r t : Int64.eq r t = Z.eqb (Int64.unsigned r) (Int64.unsigned t).
Proof.
  unfold Int64.eq. destruct (zeq (Int64.unsigned r) (Int64.unsigned t)); symmetry;
    [apply Z.eqb_eq|apply Z.eqb_neq]; assumption.
Qed.
Lemma wide_predicate_max_unsigned s :
  Int64.unsigned (Int64.repr (word_modulus (wide_log s) - 1)) = word_modulus (wide_log s) - 1.
Proof. destruct s; reflexivity. Qed.
Lemma wide_predicate_denotes s all (x : Ty.tySem (Word (wide_log s))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  wide_predicate_bit s all r = Bit.toBool (@predicate_spec (wide_log s) all Alg.CoreFunSem x).
Proof.
  intros Hr. rewrite predicate_spec_numeric. unfold wide_predicate_bit.
  destruct all; unfold predicate_numeric.
  - rewrite int64_eq_numeric, wide_predicate_max_unsigned, Hr. reflexivity.
  - rewrite int64_eq_numeric, Int64.unsigned_zero, Hr. reflexivity.
Qed.

Lemma eval_wide_predicate_expr s all e le m r :
  le!_x = Some (Vlong r) ->
  eval_expr ge0 e le m (wide_predicate_expr s all) (Vint (bit_int (wide_predicate_bit s all r))).
Proof.
  intros HX. destruct all, s; eapply eval_Ebinop.
  all: try (apply eval_Etempvar; exact HX).
  all: try apply eval_Econst_int.
  all: try apply eval_Econst_long.
  all: lazymatch goal with
    | |- _ = Some (Vint (bit_int ?b)) =>
        change (Some (Val.of_bool b) = Some (Vint (bit_int b)));
        destruct b; reflexivity
    end.
Qed.

Lemma eval_wide_predicate_composes env s all m ma mc mr me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (wide_predicate_bit s all r))] E0 me
    (Vint (bit_int (wide_predicate_bit s all r))) ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_predicate s all))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_predicate s all) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_predicate_x env s all bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s, all; reflexivity|destruct s, all; reflexivity| |exact HA].
    destruct s, all; change (list_disjoint [_dst; _src; _env] [_x; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_predicate_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s, all; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_complement_read. exact Hread.
        -- apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (bit_int (wide_predicate_bit s all r)))
             (v := Vint (bit_int (wide_predicate_bit s all r)))
             (vret := Vint (bit_int (wide_predicate_bit s all r))).
           ++ reflexivity.
           ++ unfold le_wide_predicate_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_wide_predicate_expr. unfold le_wide_predicate_x.
              rewrite PTree.gss. reflexivity.
           ++ destruct s, all; lazymatch goal with
                | |- _ = Some (Vint (bit_int ?b)) =>
                    change (sem_cast (Vint (bit_int b)) tint tbool mr = Some (Vint (bit_int b)));
                    destruct b; reflexivity
                end.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct s, all; cbn; split; solve [discriminate|reflexivity].
  - destruct s, all; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
