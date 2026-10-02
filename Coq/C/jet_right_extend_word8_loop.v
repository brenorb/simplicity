(** Actual repeated byte-writer loop shared by right_extend_8_{16,32,64}.
    INTERNAL execution witnesses must be derived from initial frame contracts
    before any of these jets counts as implementation-to-specification coverage. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_arith8_layout_exec C.jet_readBit_layout.
Require Import C.jet_extend_bit8_exec C.jet_eq256_loop C.jet_extend_word8_loop.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition right_extend_word8_function s := match s with
  E8to16 => f_simplicity_right_extend_8_16 |
  E8to32 => f_simplicity_right_extend_8_32 |
  E8to64 => f_simplicity_right_extend_8_64 end.
Definition right_extend_word8_choose := Sifthenelse (Etempvar _lsb tbool)
  (Sset _t'2 (extend_bit8_choice_expr Datatypes.true))
  (Sset _t'2 (extend_bit8_choice_expr Datatypes.false)).
Definition right_extend_word8_fill := Ssequence right_extend_word8_choose
  (frame_writer_call _simplicity_write8 tuchar tvoid (Etempvar _t'2 tint)).
Definition right_extend_word8_loop s := Sloop
  (Ssequence (Sifthenelse (extend_word8_guard s) Sskip Sbreak) right_extend_word8_fill)
  eq256_loop_step.

Lemma right_extend_word8_loop_shape s :
  (match (right_extend_word8_function s).(fn_body) with
   | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence (Ssequence _ loop) _)))) => loop
   | _ => Sskip end) = right_extend_word8_loop s.
Proof. destruct s; reflexivity. Qed.

Lemma exec_right_extend_word8_fill bl le m mf bd base bit :
  le!_lsb = Some (Vint (bit_int bit)) -> le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr base); Vint (extend_bit8_arg bit)] E0 mf Vundef ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m right_extend_word8_fill E0
    (PTree.set _t'2 (Vint (extend_bit8_arg bit)) le) mf Out_normal.
Proof.
  intros HB HD HW. unfold right_extend_word8_fill.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
  - unfold right_extend_word8_choose.
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

Fixpoint right_extend_word8_fill_run bd base bit n m mf : Prop :=
  match n with
  | O => m = mf
  | S n => exists mi,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
      [Vptr bd (Ptrofs.repr base); Vint (extend_bit8_arg bit)] E0 mi Vundef /\
    right_extend_word8_fill_run bd base bit n mi mf
  end.

Theorem exec_right_extend_word8_loop s bl le m mf bd base bit i n :
  0 <= i -> i + Z.of_nat n = extend_word8_count s ->
  le!_i = Some (Vint (Int.repr i)) -> le!_lsb = Some (Vint (bit_int bit)) ->
  le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  right_extend_word8_fill_run bd base bit n m mf ->
  exists lef,
    Clight2.exec_stmt ge0 (e_one8 bl) le m (right_extend_word8_loop s) E0 lef mf Out_normal /\
    (forall id, id <> _i -> id <> _t'2 -> lef!id = le!id).
Proof.
  revert le m i. induction n as [|n IH]; intros le m i H0 Hcount HI HB HD HR.
  - cbn [right_extend_word8_fill_run] in HR. subst mf.
    assert (Heq : i = extend_word8_count s) by (cbn in Hcount; lia).
    assert (HT : Z.ltb i (extend_word8_count s) = Datatypes.false) by (apply Z.ltb_ge; lia).
    exists le. split; [|reflexivity]. unfold right_extend_word8_loop.
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    apply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + pose proof (eval_extend_word8_guard s (e_one8 bl) le m i
        ltac:(destruct s; cbn in Heq; lia) HI) as HG. rewrite HT in HG; exact HG.
    + reflexivity.
    + constructor.
  - cbn [right_extend_word8_fill_run] in HR. destruct HR as [mi [HW HR]].
    assert (Hrange : 0 <= i < extend_word8_count s) by (cbn [Z.of_nat] in Hcount; lia).
    set (loaded := PTree.set _t'2 (Vint (extend_bit8_arg bit)) le).
    set (next := PTree.set _i (Vint (Int.repr (i + 1))) loaded).
    destruct (IH next mi (i + 1) ltac:(lia) ltac:(lia)
      ltac:(unfold next; apply PTree.gss)
      ltac:(unfold next, loaded; repeat rewrite PTree.gso by discriminate; exact HB)
      ltac:(unfold next, loaded; repeat rewrite PTree.gso by discriminate; exact HD) HR)
      as [lef [HRest HP]].
    exists lef. split.
    + unfold right_extend_word8_loop in HRest |- *.
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
        -- eapply exec_right_extend_word8_fill; eauto.
      * constructor.
      * apply exec_set. apply eval_eq256_offset; [destruct s; cbn in Hrange; lia|lia|].
        unfold loaded; rewrite PTree.gso by discriminate; exact HI.
      * exact HRest.
    + intros id Hid Hit. rewrite HP by assumption.
      unfold next, loaded. repeat rewrite PTree.gso by congruence. reflexivity.
Qed.

Definition right_extend_word8_lsb r := negb (Int.eq (Int.and r Int.one) Int.zero).
Definition right_extend_word8_lsb_expr := Ecast
  (Ebinop Oand (Etempvar _input tuchar) (Econst_int Int.one tint) tint) tbool.
Lemma eval_right_extend_word8_lsb e le m r :
  le!_input = Some (Vint r) ->
  eval_expr ge0 e le m right_extend_word8_lsb_expr (Vint (bit_int (right_extend_word8_lsb r))).
Proof.
  intros HR. eapply eval_Ecast with (v1 := Vint (Int.and r Int.one)).
  - eapply eval_Ebinop; [apply eval_Etempvar; exact HR|constructor|reflexivity].
  - change (Some (Vint (if Int.eq (Int.and r Int.one) Int.zero then Int.zero else Int.one)) =
      Some (Vint (bit_int (right_extend_word8_lsb r)))).
    unfold right_extend_word8_lsb, bit_int; destruct (Int.eq (Int.and r Int.one) Int.zero); reflexivity.
Qed.
