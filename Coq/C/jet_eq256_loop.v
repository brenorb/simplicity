(** The actual eq_256 comparison loop, including early return on mismatch.
    Array loads and writer execution remain internal premises until the
    enclosing initial-only jet contract derives them. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_eq256_array C.jet_readBit_layout.
Require Import C.jet_increment8_exec C.jet_arith8_layout_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition eq256_index := Etempvar _i tint.
Definition eq256_offset k := Ebinop Oadd eq256_index (Econst_int (Int.repr k) tint) tint.
Definition eq256_first := Ederef
  (Ebinop Oadd (Evar _arr (tarray tuint 16)) eq256_index (tptr tuint)) tuint.
Definition eq256_second := Ederef
  (Ebinop Oadd (Evar _arr (tarray tuint 16)) (eq256_offset 8) (tptr tuint)) tuint.
Definition eq256_condition := Ebinop Olt eq256_index (Econst_int (Int.repr 8) tint) tint.
Definition eq256_mismatch := Ebinop One (Etempvar _t'1 tuint) (Etempvar _t'2 tuint) tint.
Definition eq256_write bit := frame_writer_call _writeBit tbool tbool (Econst_int (bit_int bit) tint).
Definition eq256_return := Sreturn (Some (Econst_int Int.one tint)).
Definition eq256_loop_body :=
  Ssequence (Sifthenelse eq256_condition Sskip Sbreak)
    (Ssequence (Sset _t'1 eq256_first)
      (Ssequence (Sset _t'2 eq256_second)
        (Sifthenelse eq256_mismatch
          (Ssequence (eq256_write Datatypes.false) eq256_return) Sskip))).
Definition eq256_loop_step := Sset _i (eq256_offset 1).
Definition eq256_loop := Sloop eq256_loop_body eq256_loop_step.
Definition eq256_loaded le x y := PTree.set _t'2 (Vint y) (PTree.set _t'1 (Vint x) le).

Lemma eval_eq256_offset e le m i k :
  0 <= i <= 8 -> 0 <= k <= 8 -> le!_i = Some (Vint (Int.repr i)) ->
  eval_expr ge0 e le m (eq256_offset k) (Vint (Int.repr (i + k))).
Proof.
  intros HI HK HL. eapply eval_Ebinop with (v1 := Vint (Int.repr i)) (v2 := Vint (Int.repr k)).
  - apply eval_Etempvar; exact HL.
  - apply eval_Econst_int.
  - change (Some (Vint (Int.add (Int.repr i) (Int.repr k))) = Some (Vint (Int.repr (i + k)))).
    rewrite Int.add_unsigned, !Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    reflexivity.
Qed.

Lemma eval_eq256_condition e le m i :
  0 <= i <= 8 -> le!_i = Some (Vint (Int.repr i)) ->
  eval_expr ge0 e le m eq256_condition (Vint (bit_int (i <? 8))).
Proof.
  intros HI HL.
  assert (Hlt : Int.lt (Int.repr i) (Int.repr 8) = (i <? 8)).
  { unfold Int.lt. rewrite !Int.signed_repr by (change Int.min_signed with (-2147483648);
      change Int.max_signed with 2147483647; lia).
    destruct (zlt i 8); symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia. }
  eapply eval_Ebinop with (v1 := Vint (Int.repr i)) (v2 := Vint (Int.repr 8)).
  - apply eval_Etempvar; exact HL.
  - apply eval_Econst_int.
  - change (Some (Val.of_bool (Int.lt (Int.repr i) (Int.repr 8))) = Some (Vint (bit_int (i <? 8)))).
    rewrite Hlt. destruct (i <? 8); reflexivity.
Qed.
Lemma eval_eq256_mismatch bl ba le m x y :
  eval_expr ge0 (eq256_env bl ba) (eq256_loaded le x y) m eq256_mismatch
    (Vint (bit_int (negb (Int.eq x y)))).
Proof.
  eapply eval_Ebinop with (v1 := Vint x) (v2 := Vint y).
  - apply eval_Etempvar. unfold eq256_loaded; rewrite PTree.gso by discriminate; apply PTree.gss.
  - apply eval_Etempvar; apply PTree.gss.
  - change (Some (Val.of_bool (negb (Int.eq x y))) = Some (Vint (bit_int (negb (Int.eq x y))))).
    destruct (Int.eq x y); reflexivity.
Qed.
Lemma exec_eq256_write bl ba le m mf bd base bit :
  le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr base); Vint (bit_int bit)] E0 mf (Vint (bit_int bit)) ->
  Clight2.exec_stmt ge0 (eq256_env bl ba) le m (eq256_write bit) E0 le mf Out_normal.
Proof.
  intros HD HW. eapply call_frame_writer_cast with (f := f_writeBit)
    (vraw := Vint (bit_int bit)) (v := Vint (bit_int bit)) (vret := Vint (bit_int bit)).
  - reflexivity.
  - exact HD.
  - reflexivity.
  - apply symbol_writeBit.
  - apply funct_writeBit.
  - apply eval_Econst_int.
  - destruct bit; reflexivity.
  - exact HW.
Qed.

Lemma exec_eq256_loop_body bl ba le m mf bd base i x y :
  0 <= i < 8 -> le!_i = Some (Vint (Int.repr i)) ->
  le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  Mem.load Mint32 m ba (4 * i) = Some (Vint x) ->
  Mem.load Mint32 m ba (4 * (i + 8)) = Some (Vint y) ->
  (Int.eq x y = Datatypes.false ->
    Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bd (Ptrofs.repr base); Vint Int.zero] E0 mf (Vint Int.zero)) ->
  Clight2.exec_stmt ge0 (eq256_env bl ba) le m eq256_loop_body E0
    (eq256_loaded le x y) (if Int.eq x y then m else mf)
    (if Int.eq x y then Out_normal else Out_return (Some (Vint Int.one, tint))).
Proof.
  intros HI HL HD HX HY HW.
  assert (HT : (i <? 8) = Datatypes.true) by (apply Z.ltb_lt; lia).
  unfold eq256_loop_body.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le).
  - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + pose proof (eval_eq256_condition (eq256_env bl ba) le m i ltac:(lia) HL) as HCond.
      rewrite HT in HCond; exact HCond.
    + reflexivity.
    + apply exec_Sskip.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'1 (Vint x) le).
    + apply exec_set. eapply eval_eq256_array_load with (index := i).
      * lia.
      * reflexivity.
      * apply eval_Etempvar; exact HL.
      * exact HX.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
        (le1 := eq256_loaded le x y).
      * apply exec_set. eapply eval_eq256_array_load with (index := i + 8).
        -- lia.
        -- reflexivity.
        -- apply eval_eq256_offset; [lia|lia|]. rewrite PTree.gso by discriminate; exact HL.
        -- exact HY.
      * eapply exec_Sifthenelse with (v1 := Vint (bit_int (negb (Int.eq x y))))
          (b := negb (Int.eq x y)).
        -- apply eval_eq256_mismatch.
        -- destruct (Int.eq x y); reflexivity.
        -- destruct (Int.eq x y) eqn:HE.
           ++ apply exec_Sskip.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf).
              ** eapply exec_eq256_write with (bd := bd) (base := base).
                 --- unfold eq256_loaded; repeat rewrite PTree.gso by discriminate; exact HD.
                 --- exact (HW eq_refl).
              ** apply exec_Sreturn_some; apply eval_Econst_int.
Qed.

Theorem exec_eq256_loop bl ba le m mf bd base i xs ys :
  0 <= i -> i + Z.of_nat (length xs) = 8 -> length xs = length ys ->
  le!_i = Some (Vint (Int.repr i)) -> le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  (forall j x, nth_error xs j = Some x ->
    Mem.load Mint32 m ba (4 * (i + Z.of_nat j)) = Some (Vint x)) ->
  (forall j y, nth_error ys j = Some y ->
    Mem.load Mint32 m ba (4 * (i + Z.of_nat j + 8)) = Some (Vint y)) ->
  (eq256_words_equal xs ys = Datatypes.false ->
    Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bd (Ptrofs.repr base); Vint Int.zero] E0 mf (Vint Int.zero)) ->
  exists lef,
    Clight2.exec_stmt ge0 (eq256_env bl ba) le m eq256_loop E0 lef
      (if eq256_words_equal xs ys then m else mf)
      (if eq256_words_equal xs ys then Out_normal else Out_return (Some (Vint Int.one, tint))) /\
    lef!_dst = Some (Vptr bd (Ptrofs.repr base)).
Proof.
  revert le i ys. induction xs as [|x xs IH]; intros le i [|y ys] H0 Hcount Hlen HL HD HX HY HW;
    try discriminate.
  - assert (Hi : i = 8) by (cbn in Hcount; lia). subst i.
    exists le. split; [|exact HD]. unfold eq256_loop.
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    unfold eq256_loop_body. apply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + exact (eval_eq256_condition (eq256_env bl ba) le m 8 ltac:(lia) HL).
    + reflexivity.
    + apply exec_Sbreak.
  - assert (Hi : 0 <= i < 8) by (cbn [length] in Hcount; lia).
    assert (HFirst : Mem.load Mint32 m ba (4 * i) = Some (Vint x)).
    { pose proof (HX O x eq_refl) as H. replace (4 * (i + Z.of_nat O)) with (4 * i) in H by lia. exact H. }
    assert (HSecond : Mem.load Mint32 m ba (4 * (i + 8)) = Some (Vint y)).
    { pose proof (HY O y eq_refl) as H.
      replace (4 * (i + Z.of_nat O + 8)) with (4 * (i + 8)) in H by lia. exact H. }
    pose proof (exec_eq256_loop_body bl ba le m mf bd base i x y Hi HL HD HFirst HSecond
      ltac:(intros HE; apply HW; cbn [eq256_words_equal]; rewrite HE; reflexivity)) as HBody.
    destruct (Int.eq x y) eqn:HE.
    +
      cbn [eq256_words_equal] in HW |- *. rewrite HE in HW |- *. cbn [andb] in HW |- *.
      set (next := PTree.set _i (Vint (Int.repr (i + 1))) (eq256_loaded le x y)).
      assert (HStep : Clight2.exec_stmt ge0 (eq256_env bl ba) (eq256_loaded le x y) m
        eq256_loop_step E0 next m Out_normal).
      { apply exec_set. apply eval_eq256_offset; [lia|lia|].
        unfold eq256_loaded; repeat rewrite PTree.gso by discriminate; exact HL. }
      destruct (IH next (i + 1) ys ltac:(lia) ltac:(cbn [length] in Hcount; lia)
        ltac:(cbn [length] in Hlen; lia) ltac:(unfold next; apply PTree.gss)
        ltac:(unfold next, eq256_loaded; repeat rewrite PTree.gso by discriminate; exact HD)
        ltac:(intros j v Hv; pose proof (HX (S j) v Hv) as H;
          replace (4 * (i + Z.of_nat (S j))) with (4 * (i + 1 + Z.of_nat j)) in H by lia; exact H)
        ltac:(intros j v Hv; pose proof (HY (S j) v Hv) as H;
          replace (4 * (i + Z.of_nat (S j) + 8)) with (4 * (i + 1 + Z.of_nat j + 8)) in H by lia; exact H)
        HW) as [lef [HRest HDst]].
      exists lef. split; [|exact HDst]. unfold eq256_loop in HRest |- *.
      eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0)
        (le1 := eq256_loaded le x y) (m1 := m) (out1 := Out_normal) (le2 := next) (m2 := m);
        [exact HBody|constructor|exact HStep|exact HRest].
    + exists (eq256_loaded le x y). split.
      * cbn [eq256_words_equal]. rewrite HE. unfold eq256_loop.
        eapply exec_Sloop_stop1; [exact HBody|constructor].
      * unfold eq256_loaded; repeat rewrite PTree.gso by discriminate; exact HD.
Qed.

Theorem exec_eq256_compare bl ba le m mf bd base xs ys :
  length xs = 8%nat -> length ys = 8%nat ->
  le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  (forall j x, nth_error xs j = Some x ->
    Mem.load Mint32 m ba (4 * Z.of_nat j) = Some (Vint x)) ->
  (forall j y, nth_error ys j = Some y ->
    Mem.load Mint32 m ba (4 * (Z.of_nat j + 8)) = Some (Vint y)) ->
  Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr base); Vint (bit_int (eq256_words_equal xs ys))]
    E0 mf (Vint (bit_int (eq256_words_equal xs ys))) ->
  exists lef, Clight2.exec_stmt ge0 (eq256_env bl ba) le m
    (Ssequence (Ssequence (Sset _i (Econst_int Int.zero tint)) eq256_loop)
      (Ssequence (eq256_write Datatypes.true) eq256_return))
    E0 lef mf (Out_return (Some (Vint Int.one, tint))).
Proof.
  intros HXlen HYlen HD HX HY HW.
  set (start := PTree.set _i (Vint Int.zero) le).
  destruct (exec_eq256_loop bl ba start m mf bd base 0 xs ys ltac:(lia)
    ltac:(rewrite HXlen; reflexivity) ltac:(congruence)
    ltac:(unfold start; apply PTree.gss)
    ltac:(unfold start; rewrite PTree.gso by discriminate; exact HD)
    ltac:(intros j x Hj; change (Mem.load Mint32 m ba (4 * Z.of_nat j) = Some (Vint x)); apply HX; exact Hj)
    ltac:(intros j y Hj; change (Mem.load Mint32 m ba (4 * (Z.of_nat j + 8)) = Some (Vint y)); apply HY; exact Hj)
    ltac:(intros HE; rewrite HE in HW; exact HW)) as [lef [HLoop HDst]].
  exists lef.
  destruct (eq256_words_equal xs ys) eqn:HE.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := lef).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := start).
      * apply exec_set; apply eval_Econst_int.
      * exact HLoop.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := lef).
      * eapply exec_eq256_write; [exact HDst|exact HW].
      * apply exec_Sreturn_some; apply eval_Econst_int.
  - apply exec_Sseq_2; [|discriminate].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := start).
    + apply exec_set; apply eval_Econst_int.
    + exact HLoop.
Qed.
