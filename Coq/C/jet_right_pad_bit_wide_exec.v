(** Exact right_pad_low_1_{16,32,64} casts, shifts and full function boundary. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_readBit_layout C.jet_complement1_exec C.jet_wide C.jet_wide_spec C.jet_spec C.jet_pad_bit_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_right_pad_bit s := match s with
  W16 => f_simplicity_right_pad_low_1_16 | W32 => f_simplicity_right_pad_low_1_32
  | W64 => f_simplicity_right_pad_low_1_64 end.
Definition le_wide_right_pad_bit env s bd dofs bs sofs bit :=
  PTree.set _bit (Vint (bit_int bit)) (PTree.set _t'1 (Vint (bit_int bit))
    (le_arith8_layout env (wide_right_pad_bit s) bd dofs bs sofs)).

Definition wide_right_pad_bit_expr s :=
  Ecast (Ebinop Oshl (Ecast (Etempvar _bit tbool) tulong)
    (Ebinop Osub (Econst_int (Int.repr (wide_bits s)) tint)
      (Econst_int Int.one tint) tint) tulong) tulong.
Lemma right_pad_shift_sub s :
  Int.sub (Int.repr (wide_bits s)) Int.one = Int.repr (wide_bits s - 1).
Proof. destruct s; vm_compute; reflexivity. Qed.
Lemma right_pad_shift_guard s : Int.ltu (Int.repr (wide_bits s - 1)) Int64.iwordsize' = Datatypes.true.
Proof. destruct s; vm_compute; reflexivity. Qed.

Lemma eval_wide_right_pad_bit_expr e le m s bit :
  le!_bit = Some (Vint (bit_int bit)) ->
  eval_expr ge0 e le m (wide_right_pad_bit_expr s) (Vlong (right_pad_bit_long s bit)).
Proof.
  intros HB. unfold wide_right_pad_bit_expr, right_pad_bit_long.
  eapply eval_Ecast with (v1 := Vlong (Int64.shl (bit_long bit) (Int64.repr (wide_bits s - 1)))).
  - eapply eval_Ebinop with (v1 := Vlong (bit_long bit)) (v2 := Vint (Int.repr (wide_bits s - 1))).
    + eapply eval_Ecast with (v1 := Vint (bit_int bit)).
      * eapply eval_Etempvar; exact HB.
      * unfold bit_int, bit_long; destruct bit; reflexivity.
    + eapply eval_Ebinop with (v1 := Vint (Int.repr (wide_bits s))) (v2 := Vint Int.one).
      * apply eval_Econst_int.
      * apply eval_Econst_int.
      * change (Some (Vint (Int.sub (Int.repr (wide_bits s)) Int.one)) =
          Some (Vint (Int.repr (wide_bits s - 1)))). rewrite right_pad_shift_sub; reflexivity.
    + change ((if Int.ltu (Int.repr (wide_bits s - 1)) Int64.iwordsize'
        then Some (Vlong (Int64.shl (bit_long bit) (Int64.repr (Int.unsigned (Int.repr (wide_bits s - 1))))))
        else None) = Some (Vlong (Int64.shl (bit_long bit) (Int64.repr (wide_bits s - 1))))).
      rewrite right_pad_shift_guard, Int.unsigned_repr by
        (pose proof (wide_bits_bounds s); change Int.max_unsigned with 4294967295; lia).
      reflexivity.
  - reflexivity.
Qed.

Lemma wide_right_pad_bit_body s : (wide_right_pad_bit s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence bit_jet_read (Sset _bit (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence (frame_writer_call (wide_writer_id s) tulong tvoid (wide_right_pad_bit_expr s))
        (Sreturn (Some (Econst_int Int.one tint))))).
Proof. destruct s; reflexivity. Qed.

Lemma eval_wide_right_pad_bit_composes env s m ma mc mr me mf bl bd dbase bs sbase bytes bit :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int bit)) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (right_pad_bit_long s bit)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_right_pad_bit s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_right_pad_bit s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_right_pad_bit env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bit)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s; change (list_disjoint [_dst; _src; _env] [_bit; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_right_pad_bit_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_right_pad_bit env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bit).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_bit_jet_read. exact Hread.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int bit)).
           ++ eapply eval_Etempvar; rewrite PTree.gss; reflexivity.
           ++ unfold bit_int; destruct bit; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := wide_writer s)
             (vraw := Vlong (right_pad_bit_long s bit)) (v := Vlong (right_pad_bit_long s bit)) (vret := Vundef).
           ++ destruct s; reflexivity.
           ++ unfold le_wide_right_pad_bit, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
           ++ destruct s; reflexivity.
           ++ apply wide_writer_symbol.
           ++ apply wide_writer_funct.
           ++ apply eval_wide_right_pad_bit_expr. unfold le_wide_right_pad_bit.
              rewrite PTree.gss; reflexivity.
           ++ reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some; apply eval_Econst_int.
  - destruct s; cbn; split; solve [discriminate | reflexivity].
  - destruct s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
