(** Actual repeated wide-writer loop for left_extend_{16_32,16_64,32_64}.
    Internal call witnesses are discharged by initial-only consumer proofs. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_arith8_layout_exec C.jet_readBit_layout.
Require Import C.jet_extend_bit_wide_exec C.jet_eq256_loop C.jet_wide C.jet_pad_bit_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Inductive extend_wide_size := E16to32 | E16to64 | E32to64.
Definition extend_wide_input s := match s with E16to32 | E16to64 => W16 | E32to64 => W32 end.
Definition extend_wide_output s := match s with E16to32 => W32 | E16to64 | E32to64 => W64 end.
Definition extend_wide_bits s := wide_bits (extend_wide_output s).
Definition extend_wide_count s := match s with E16to32 => 1 | E16to64 => 3 | E32to64 => 1 end.
Definition extend_wide_function s := match s with
  E16to32 => f_simplicity_left_extend_16_32 |
  E16to64 => f_simplicity_left_extend_16_64 |
  E32to64 => f_simplicity_left_extend_32_64 end.
Definition extend_wide_limit s := Ebinop Osub
  (Ebinop Odiv (Econst_int (Int.repr (extend_wide_bits s)) tint)
    (Econst_int (Int.repr (wide_bits (extend_wide_input s))) tint) tint) (Econst_int Int.one tint) tint.
Definition extend_wide_guard s := Ebinop Olt eq256_index (extend_wide_limit s) tint.
Definition extend_wide_choose s := Sifthenelse (Etempvar _msb tbool)
  (Sset _t'2 (extend_bit_choice_expr (extend_wide_input s) Datatypes.true))
  (Sset _t'2 (extend_bit_choice_expr (extend_wide_input s) Datatypes.false)).
Definition extend_wide_fill s := Ssequence (extend_wide_choose s)
  (frame_writer_call (wide_writer_id (extend_wide_input s)) tulong tvoid
    (Etempvar _t'2 (extend_bit_type (extend_wide_input s)))).
Definition extend_wide_loop s := Sloop
  (Ssequence (Sifthenelse (extend_wide_guard s) Sskip Sbreak) (extend_wide_fill s))
  eq256_loop_step.

Lemma extend_wide_loop_shape s :
  (match (extend_wide_function s).(fn_body) with
   | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence (Ssequence _ loop) _))) => loop
   | _ => Sskip end) = extend_wide_loop s.
Proof. destruct s; reflexivity. Qed.

Lemma eval_extend_wide_limit s e le m :
  eval_expr ge0 e le m (extend_wide_limit s) (Vint (Int.repr (extend_wide_count s))).
Proof.
  unfold extend_wide_limit. eapply eval_Ebinop.
  - eapply eval_Ebinop; [constructor|constructor|destruct s; reflexivity].
  - constructor.
  - destruct s; reflexivity.
Qed.

Lemma eval_extend_wide_guard s e le m i :
  0 <= i <= 16 -> le!_i = Some (Vint (Int.repr i)) ->
  eval_expr ge0 e le m (extend_wide_guard s)
    (Vint (bit_int (Z.ltb i (extend_wide_count s)))).
Proof.
  intros Hi HL.
  assert (Hlt : Int.lt (Int.repr i) (Int.repr (extend_wide_count s)) =
    Z.ltb i (extend_wide_count s)).
  { unfold Int.lt. rewrite !Int.signed_repr by
      (destruct s; change Int.min_signed with (-2147483648);
        change Int.max_signed with 2147483647; cbn; lia).
    destruct (zlt i (extend_wide_count s)); symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia. }
  eapply eval_Ebinop.
  - apply eval_Etempvar; exact HL.
  - apply eval_extend_wide_limit.
  - change (Some (Val.of_bool (Int.lt (Int.repr i) (Int.repr (extend_wide_count s)))) =
      Some (Vint (bit_int (Z.ltb i (extend_wide_count s))))).
    rewrite Hlt. destruct (Z.ltb i (extend_wide_count s)); reflexivity.
Qed.

Lemma exec_extend_wide_fill s bl le m mf bd base bit :
  le!_msb = Some (Vint (bit_int bit)) -> le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  Clight2.eval_funcall ge0 m (Internal (wide_writer (extend_wide_input s)))
    [Vptr bd (Ptrofs.repr base); Vlong (extend_bit_long (extend_wide_input s) bit)] E0 mf Vundef ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m (extend_wide_fill s) E0
    (PTree.set _t'2 (extend_bit_raw (extend_wide_input s) bit) le) mf Out_normal.
Proof.
  intros HB HD HW. unfold extend_wide_fill.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
  - unfold extend_wide_choose.
    eapply exec_Sifthenelse with (v1 := Vint (bit_int bit)) (b := bit).
    + apply eval_Etempvar; exact HB.
    + unfold bit_int; destruct bit; reflexivity.
    + destruct bit; apply exec_set; apply eval_extend_bit_choice_expr.
  - eapply call_frame_writer_cast with (f := wide_writer (extend_wide_input s))
      (vraw := extend_bit_raw (extend_wide_input s) bit) (v := Vlong (extend_bit_long (extend_wide_input s) bit)) (vret := Vundef).
    + destruct s; reflexivity.
    + rewrite PTree.gso by discriminate; exact HD.
    + destruct s; reflexivity.
    + apply wide_writer_symbol.
    + apply wide_writer_funct.
    + apply eval_Etempvar; apply PTree.gss.
    + apply extend_bit_raw_cast.
    + exact HW.
Qed.

Fixpoint extend_wide_fill_run s bd base bit n m mf : Prop :=
  match n with
  | O => m = mf
  | S n => exists mi,
    Clight2.eval_funcall ge0 m (Internal (wide_writer (extend_wide_input s)))
      [Vptr bd (Ptrofs.repr base); Vlong (extend_bit_long (extend_wide_input s) bit)] E0 mi Vundef /\
    extend_wide_fill_run s bd base bit n mi mf
  end.

Theorem exec_extend_wide_loop s bl le m mf bd base bit i n :
  0 <= i -> i + Z.of_nat n = extend_wide_count s ->
  le!_i = Some (Vint (Int.repr i)) -> le!_msb = Some (Vint (bit_int bit)) ->
  le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  extend_wide_fill_run s bd base bit n m mf ->
  exists lef,
    Clight2.exec_stmt ge0 (e_one8 bl) le m (extend_wide_loop s) E0 lef mf Out_normal /\
    (forall id, id <> _i -> id <> _t'2 -> lef!id = le!id).
Proof.
  revert le m i. induction n as [|n IH]; intros le m i H0 Hcount HI HB HD HR.
  - cbn [extend_wide_fill_run] in HR. subst mf.
    assert (Heq : i = extend_wide_count s) by (cbn in Hcount; lia).
    assert (HT : Z.ltb i (extend_wide_count s) = Datatypes.false) by (apply Z.ltb_ge; lia).
    exists le. split; [|reflexivity]. unfold extend_wide_loop.
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    apply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + pose proof (eval_extend_wide_guard s (e_one8 bl) le m i
        ltac:(destruct s; cbn in Heq; lia) HI) as HG. rewrite HT in HG; exact HG.
    + reflexivity.
    + constructor.
  - cbn [extend_wide_fill_run] in HR. destruct HR as [mi [HW HR]].
    assert (Hrange : 0 <= i < extend_wide_count s) by (cbn [Z.of_nat] in Hcount; lia).
    set (loaded := PTree.set _t'2 (extend_bit_raw (extend_wide_input s) bit) le).
    set (next := PTree.set _i (Vint (Int.repr (i + 1))) loaded).
    destruct (IH next mi (i + 1) ltac:(lia) ltac:(lia)
      ltac:(unfold next; apply PTree.gss)
      ltac:(unfold next, loaded; repeat rewrite PTree.gso by discriminate; exact HB)
      ltac:(unfold next, loaded; repeat rewrite PTree.gso by discriminate; exact HD) HR)
      as [lef [HRest HP]].
    exists lef. split.
    + unfold extend_wide_loop in HRest |- *.
      eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0)
        (le1 := loaded) (m1 := mi) (out1 := Out_normal) (le2 := next) (m2 := mi).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
        -- eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
           ++ pose proof (eval_extend_wide_guard s (e_one8 bl) le m i
                ltac:(destruct s; cbn in Hrange; lia) HI) as HG.
              assert (HT : Z.ltb i (extend_wide_count s) = Datatypes.true)
                by (apply Z.ltb_lt; lia).
              rewrite HT in HG; exact HG.
           ++ reflexivity.
           ++ constructor.
        -- eapply exec_extend_wide_fill; eauto.
      * constructor.
      * apply exec_set. apply eval_eq256_offset; [destruct s; cbn in Hrange; lia|lia|].
        unfold loaded; rewrite PTree.gso by discriminate; exact HI.
      * exact HRest.
    + intros id Hid Hit. rewrite HP by assumption.
      unfold next, loaded. repeat rewrite PTree.gso by congruence. reflexivity.
Qed.
