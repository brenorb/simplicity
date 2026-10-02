(** Actual repeated byte-writer loop shared by left_extend_8_{16,32,64}.
    INTERNAL execution witnesses must be derived from initial frame contracts
    before any of these jets counts as implementation-to-specification coverage. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_arith8_layout_exec C.jet_readBit_layout.
Require Import C.jet_extend_bit8_exec C.jet_eq256_loop.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Inductive extend_word8_size := E8to16 | E8to32 | E8to64.
Definition extend_word8_bits s := match s with E8to16 => 16 | E8to32 => 32 | E8to64 => 64 end.
Definition extend_word8_count s := match s with E8to16 => 1 | E8to32 => 3 | E8to64 => 7 end.
Definition extend_word8_function s := match s with
  E8to16 => f_simplicity_left_extend_8_16 |
  E8to32 => f_simplicity_left_extend_8_32 |
  E8to64 => f_simplicity_left_extend_8_64 end.
Definition extend_word8_limit s := Ebinop Osub
  (Ebinop Odiv (Econst_int (Int.repr (extend_word8_bits s)) tint)
    (Econst_int (Int.repr 8) tint) tint) (Econst_int Int.one tint) tint.
Definition extend_word8_guard s := Ebinop Olt eq256_index (extend_word8_limit s) tint.
Definition extend_word8_choose := Sifthenelse (Etempvar _msb tbool)
  (Sset _t'2 (extend_bit8_choice_expr Datatypes.true))
  (Sset _t'2 (extend_bit8_choice_expr Datatypes.false)).
Definition extend_word8_fill := Ssequence extend_word8_choose
  (frame_writer_call _simplicity_write8 tuchar tvoid (Etempvar _t'2 tint)).
Definition extend_word8_loop s := Sloop
  (Ssequence (Sifthenelse (extend_word8_guard s) Sskip Sbreak) extend_word8_fill)
  eq256_loop_step.

Lemma extend_word8_loop_shape s :
  (match (extend_word8_function s).(fn_body) with
   | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence (Ssequence _ loop) _))) => loop
   | _ => Sskip end) = extend_word8_loop s.
Proof. destruct s; reflexivity. Qed.

Lemma eval_extend_word8_limit s e le m :
  eval_expr ge0 e le m (extend_word8_limit s) (Vint (Int.repr (extend_word8_count s))).
Proof.
  unfold extend_word8_limit. eapply eval_Ebinop.
  - eapply eval_Ebinop; [constructor|constructor|destruct s; reflexivity].
  - constructor.
  - destruct s; reflexivity.
Qed.

Lemma eval_extend_word8_guard s e le m i :
  0 <= i <= 16 -> le!_i = Some (Vint (Int.repr i)) ->
  eval_expr ge0 e le m (extend_word8_guard s)
    (Vint (bit_int (Z.ltb i (extend_word8_count s)))).
Proof.
  intros Hi HL.
  assert (Hlt : Int.lt (Int.repr i) (Int.repr (extend_word8_count s)) =
    Z.ltb i (extend_word8_count s)).
  { unfold Int.lt. rewrite !Int.signed_repr by
      (destruct s; change Int.min_signed with (-2147483648);
        change Int.max_signed with 2147483647; cbn; lia).
    destruct (zlt i (extend_word8_count s)); symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia. }
  eapply eval_Ebinop.
  - apply eval_Etempvar; exact HL.
  - apply eval_extend_word8_limit.
  - change (Some (Val.of_bool (Int.lt (Int.repr i) (Int.repr (extend_word8_count s)))) =
      Some (Vint (bit_int (Z.ltb i (extend_word8_count s))))).
    rewrite Hlt. destruct (Z.ltb i (extend_word8_count s)); reflexivity.
Qed.

Lemma exec_extend_word8_fill bl le m mf bd base bit :
  le!_msb = Some (Vint (bit_int bit)) -> le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr base); Vint (extend_bit8_arg bit)] E0 mf Vundef ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m extend_word8_fill E0
    (PTree.set _t'2 (Vint (extend_bit8_arg bit)) le) mf Out_normal.
Proof.
  intros HB HD HW. unfold extend_word8_fill.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
  - unfold extend_word8_choose.
    eapply exec_Sifthenelse with (v1 := Vint (bit_int bit)) (b := bit).
    + apply eval_Etempvar; exact HB.
    + unfold bit_int; destruct bit; reflexivity.
    + destruct bit; apply exec_set; apply eval_extend_bit8_choice_expr.
  - eapply call_frame_writer_cast with (f := f_simplicity_write8)
      (vraw := Vint (extend_bit8_arg bit)) (v := Vint (extend_bit8_arg bit)) (vret := Vundef).
    + reflexivity.
    + rewrite PTree.gso by discriminate; exact HD.
    + reflexivity.
    + apply symbol_write8.
    + apply funct_write8.
    + apply eval_Etempvar; apply PTree.gss.
    + apply extend_bit8_cast.
    + exact HW.
Qed.

Fixpoint extend_word8_fill_run bd base bit n m mf : Prop :=
  match n with
  | O => m = mf
  | S n => exists mi,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
      [Vptr bd (Ptrofs.repr base); Vint (extend_bit8_arg bit)] E0 mi Vundef /\
    extend_word8_fill_run bd base bit n mi mf
  end.

Theorem exec_extend_word8_loop s bl le m mf bd base bit i n :
  0 <= i -> i + Z.of_nat n = extend_word8_count s ->
  le!_i = Some (Vint (Int.repr i)) -> le!_msb = Some (Vint (bit_int bit)) ->
  le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  extend_word8_fill_run bd base bit n m mf ->
  exists lef,
    Clight2.exec_stmt ge0 (e_one8 bl) le m (extend_word8_loop s) E0 lef mf Out_normal /\
    (forall id, id <> _i -> id <> _t'2 -> lef!id = le!id).
Proof.
  revert le m i. induction n as [|n IH]; intros le m i H0 Hcount HI HB HD HR.
  - cbn [extend_word8_fill_run] in HR. subst mf.
    assert (Heq : i = extend_word8_count s) by (cbn in Hcount; lia).
    assert (HT : Z.ltb i (extend_word8_count s) = Datatypes.false) by (apply Z.ltb_ge; lia).
    exists le. split; [|reflexivity]. unfold extend_word8_loop.
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    apply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + pose proof (eval_extend_word8_guard s (e_one8 bl) le m i
        ltac:(destruct s; cbn in Heq; lia) HI) as HG. rewrite HT in HG; exact HG.
    + reflexivity.
    + constructor.
  - cbn [extend_word8_fill_run] in HR. destruct HR as [mi [HW HR]].
    assert (Hrange : 0 <= i < extend_word8_count s) by (cbn [Z.of_nat] in Hcount; lia).
    set (loaded := PTree.set _t'2 (Vint (extend_bit8_arg bit)) le).
    set (next := PTree.set _i (Vint (Int.repr (i + 1))) loaded).
    destruct (IH next mi (i + 1) ltac:(lia) ltac:(lia)
      ltac:(unfold next; apply PTree.gss)
      ltac:(unfold next, loaded; repeat rewrite PTree.gso by discriminate; exact HB)
      ltac:(unfold next, loaded; repeat rewrite PTree.gso by discriminate; exact HD) HR)
      as [lef [HRest HP]].
    exists lef. split.
    + unfold extend_word8_loop in HRest |- *.
      eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0)
        (le1 := loaded) (m1 := mi) (out1 := Out_normal) (le2 := next) (m2 := mi).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
        -- eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
           ++ pose proof (eval_extend_word8_guard s (e_one8 bl) le m i
                ltac:(destruct s; cbn in Hrange; lia) HI) as HG.
              assert (HT : Z.ltb i (extend_word8_count s) = Datatypes.true)
                by (apply Z.ltb_lt; lia).
              rewrite HT in HG; exact HG.
           ++ reflexivity.
           ++ constructor.
        -- eapply exec_extend_word8_fill; eauto.
      * constructor.
      * apply exec_set. apply eval_eq256_offset; [destruct s; cbn in Hrange; lia|lia|].
        unfold loaded; rewrite PTree.gso by discriminate; exact HI.
      * exact HRest.
    + intros id Hid Hit. rewrite HP by assumption.
      unfold next, loaded. repeat rewrite PTree.gso by congruence. reflexivity.
Qed.
