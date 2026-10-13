(** Direct loop support for the unchanged original field-clear helper.
    These results are not a registered jet contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Memory Events ClightBigstep.
Require Import C.jet_exec C.jet_secp_linkage C.jets_secp.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fe_clear_guard :=
  Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 5) tint) tint.
Definition fe_clear_store :=
  Sassign
    (Ederef (Ebinop Oadd
      (Efield (Ederef (Etempvar _a (tptr (Tstruct __5467 noattr)))
        (Tstruct __5467 noattr)) _n (tarray tulong 5))
      (Etempvar _i tint) (tptr tulong)) tulong)
    (Econst_int (Int.repr 0) tint).
Definition fe_clear_step :=
  Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint).
Definition fe_clear_loop :=
  Sloop (Ssequence (Sifthenelse fe_clear_guard Sskip Sbreak) fe_clear_store) fe_clear_step.
Lemma fe_clear_body_shape : fn_body f_secp256k1_fe_clear =
  Ssequence (Sset _i (Econst_int (Int.repr 0) tint)) fe_clear_loop.
Proof. reflexivity. Qed.

Lemma eval_fe_clear_guard le m i :
  0 <= i <= 5 -> le!_i = Some (Vint (Int.repr i)) ->
  eval_expr secp_ge empty_env le m fe_clear_guard
    (Vint (if Z.ltb i 5 then Int.one else Int.zero)).
Proof.
  intros Hi HIndex. unfold fe_clear_guard.
  eapply eval_Ebinop with (v1 := Vint (Int.repr i)) (v2 := Vint (Int.repr 5)).
  - apply eval_Etempvar; exact HIndex.
  - apply eval_Econst_int.
  - change (Some (Val.of_bool (Int.lt (Int.repr i) (Int.repr 5))) =
      Some (Vint (if Z.ltb i 5 then Int.one else Int.zero))).
    unfold Int.lt. rewrite Int.signed_repr by (change Int.min_signed with (-2147483648);
      change Int.max_signed with 2147483647; lia).
    change (Int.signed (Int.repr 5)) with 5.
    destruct (zlt i 5), (Z.ltb_spec i 5); try lia; reflexivity.
Qed.

Lemma fe_clear_composite_members :
  option_map co_members ((genv_cenv secp_ge)!__5467) =
  Some [Member_plain _n (tarray tulong 5)].
Proof. vm_compute; reflexivity. Qed.
Lemma fe_clear_field_layout : exists co,
  (genv_cenv secp_ge)!__5467 = Some co /\
  field_offset secp_ge _n (co_members co) = Errors.OK (0, Full).
Proof.
  pose proof fe_clear_composite_members as HM.
  destruct ((genv_cenv secp_ge)!__5467) as [co|] eqn:HC; [|discriminate].
  inversion HM as [HMembers].
  exists co; split; [reflexivity|].
  rewrite HMembers. reflexivity.
Qed.

Lemma eval_fe_clear_limb_array le m b base :
  le!_a = Some (Vptr b (Ptrofs.repr base)) ->
  eval_expr secp_ge empty_env le m
    (Efield (Ederef (Etempvar _a (tptr (Tstruct __5467 noattr)))
      (Tstruct __5467 noattr)) _n (tarray tulong 5))
    (Vptr b (Ptrofs.repr base)).
Proof.
  intro HA. destruct fe_clear_field_layout as [co [HC HO]].
  rewrite <- (Ptrofs.add_zero (Ptrofs.repr base)).
  eapply eval_Elvalue.
  - eapply eval_Efield_struct with (co := co) (delta := 0).
    + eapply eval_Elvalue.
      * apply eval_Ederef. apply eval_Etempvar; exact HA.
      * apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HC.
    + exact HO.
  - apply deref_loc_reference; reflexivity.
Qed.

Lemma exec_fe_clear_guard_continue le m i :
  0 <= i < 5 -> le!_i = Some (Vint (Int.repr i)) ->
  Clight2.exec_stmt secp_ge empty_env le m
    (Sifthenelse fe_clear_guard Sskip Sbreak) E0 le m Out_normal.
Proof.
  intros Hi HIndex.
  eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
  - pose proof (eval_fe_clear_guard le m i ltac:(lia) HIndex) as H.
    rewrite (proj2 (Z.ltb_lt i 5) ltac:(lia)) in H; exact H.
  - reflexivity.
  - apply exec_Sskip.
Qed.

Lemma exec_fe_clear_guard_stop le m :
  le!_i = Some (Vint (Int.repr 5)) ->
  Clight2.exec_stmt secp_ge empty_env le m
    (Sifthenelse fe_clear_guard Sskip Sbreak) E0 le m Out_break.
Proof.
  intro HIndex.
  eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
  - exact (eval_fe_clear_guard le m 5 ltac:(lia) HIndex).
  - reflexivity.
  - apply exec_Sbreak.
Qed.

Lemma exec_fe_clear_index_step le m i :
  0 <= i < 5 -> le!_i = Some (Vint (Int.repr i)) ->
  Clight2.exec_stmt secp_ge empty_env le m fe_clear_step E0
    (PTree.set _i (Vint (Int.repr (i + 1))) le) m Out_normal.
Proof.
  intros Hi HIndex. apply exec_set.
  eapply eval_Ebinop with (v1 := Vint (Int.repr i)) (v2 := Vint Int.one).
  - apply eval_Etempvar; exact HIndex.
  - apply eval_Econst_int.
  - change (Some (Vint (Int.add (Int.repr i) Int.one)) =
      Some (Vint (Int.repr (i + 1)))).
    unfold Int.add. rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    reflexivity.
Qed.

Lemma eval_fe_clear_limb_pointer le m b base i :
  0 <= base -> base + 40 <= Ptrofs.max_unsigned -> 0 <= i < 5 ->
  le!_a = Some (Vptr b (Ptrofs.repr base)) ->
  le!_i = Some (Vint (Int.repr i)) ->
  eval_expr secp_ge empty_env le m
    (Ebinop Oadd
      (Efield (Ederef (Etempvar _a (tptr (Tstruct __5467 noattr)))
        (Tstruct __5467 noattr)) _n (tarray tulong 5))
      (Etempvar _i tint) (tptr tulong))
    (Vptr b (Ptrofs.repr (base + 8 * i))).
Proof.
  intros HB HM Hi HA HI.
  eapply eval_Ebinop with (v1 := Vptr b (Ptrofs.repr base)) (v2 := Vint (Int.repr i)).
  - apply eval_fe_clear_limb_array; exact HA.
  - apply eval_Etempvar; exact HI.
  - change (Some (Vptr b (Ptrofs.add (Ptrofs.repr base)
      (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.repr (Int.signed (Int.repr i)))))) =
      Some (Vptr b (Ptrofs.repr (base + 8 * i)))).
    rewrite Int.signed_repr by (change Int.min_signed with (-2147483648);
      change Int.max_signed with 2147483647; lia).
    unfold Ptrofs.mul. rewrite !Ptrofs.unsigned_repr by lia.
    unfold Ptrofs.add. rewrite !Ptrofs.unsigned_repr by lia. reflexivity.
Qed.

Lemma exec_fe_clear_limb_store le m mi b base i :
  0 <= base -> base + 40 <= Ptrofs.max_unsigned -> 0 <= i < 5 ->
  le!_a = Some (Vptr b (Ptrofs.repr base)) ->
  le!_i = Some (Vint (Int.repr i)) ->
  Mem.store Mint64 m b (base + 8 * i) (Vlong Int64.zero) = Some mi ->
  Clight2.exec_stmt secp_ge empty_env le m fe_clear_store E0 le mi Out_normal.
Proof.
  intros HB HM Hi HA HI HS. unfold fe_clear_store.
  eapply exec_Sassign with (loc := b) (ofs := Ptrofs.repr (base + 8 * i))
    (bf := Full) (v2 := Vint Int.zero) (v := Vlong Int64.zero).
  - apply eval_Ederef. apply eval_fe_clear_limb_pointer; assumption.
  - apply eval_Econst_int.
  - reflexivity.
  - eapply assign_loc_value with (chunk := Mint64); [reflexivity|].
    unfold Mem.storev. rewrite Ptrofs.unsigned_repr by lia. exact HS.
Qed.

Fixpoint fe_clear_stores (n : nat) b base i m mf : Prop :=
  match n with
  | O => m = mf
  | S rest => exists mi,
      Mem.store Mint64 m b (base + 8 * i) (Vlong Int64.zero) = Some mi /\
      fe_clear_stores rest b base (i + 1) mi mf
  end.

Lemma exec_fe_clear_loop_from_stores n b base mf :
  forall le m i,
  0 <= base -> base + 40 <= Ptrofs.max_unsigned ->
  0 <= i -> i + Z.of_nat n = 5 ->
  le!_a = Some (Vptr b (Ptrofs.repr base)) ->
  le!_i = Some (Vint (Int.repr i)) ->
  fe_clear_stores n b base i m mf ->
  exists lef, Clight2.exec_stmt secp_ge empty_env le m fe_clear_loop E0 lef mf Out_normal.
Proof.
  induction n as [|n IH]; intros le m i HB HM Hi HEnd HA HI HR.
  - change (m = mf) in HR; subst mf.
    assert (i = 5) by (cbn in HEnd; lia); subst i.
    exists le. unfold fe_clear_loop.
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    apply exec_Sseq_2; [apply exec_fe_clear_guard_stop; exact HI|discriminate].
  - destruct HR as [mi [HS HR]].
    assert (HBound : 0 <= i < 5) by (rewrite Nat2Z.inj_succ in HEnd;
      pose proof (Nat2Z.is_nonneg n); lia).
    set (next := PTree.set _i (Vint (Int.repr (i + 1))) le).
    destruct (IH next mi (i + 1) HB HM ltac:(lia)
      ltac:(rewrite Nat2Z.inj_succ in HEnd; lia)
      ltac:(unfold next; rewrite PTree.gso by discriminate; exact HA)
      ltac:(unfold next; apply PTree.gss) HR) as [lef HRest].
    exists lef. unfold fe_clear_loop in HRest |- *.
    eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0)
      (le1 := le) (m1 := mi) (out1 := Out_normal) (le2 := next) (m2 := mi).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
      * apply exec_fe_clear_guard_continue with (i := i); assumption.
      * apply exec_fe_clear_limb_store with (b := b) (base := base) (i := i); assumption.
    + constructor.
    + apply exec_fe_clear_index_step; assumption.
    + exact HRest.
Qed.

Definition fe_clear_env b base :=
  PTree.set _a (Vptr b (Ptrofs.repr base)) (create_undef_temps (fn_temps f_secp256k1_fe_clear)).
Lemma fe_clear_entry m b base :
  function_entry2 secp_ge f_secp256k1_fe_clear [Vptr b (Ptrofs.repr base)]
    m empty_env (fe_clear_env b base) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor; simpl; intuition discriminate.
  - intros x y HX HY HE. cbn in HX, HY.
    destruct HX as [HX|HX], HY as [HY|HY]; try contradiction.
    subst x y; discriminate.
  - constructor.
  - reflexivity.
Qed.

Theorem eval_fe_clear_from_stores m mf b base :
  0 <= base -> base + 40 <= Ptrofs.max_unsigned ->
  fe_clear_stores 5 b base 0 m mf ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_clear)
    [Vptr b (Ptrofs.repr base)] E0 mf Vundef.
Proof.
  intros HB HM HR.
  set (le := fe_clear_env b base).
  set (start := PTree.set _i (Vint Int.zero) le).
  destruct (exec_fe_clear_loop_from_stores 5 b base mf start m 0 HB HM
    ltac:(lia) eq_refl
    ltac:(unfold start, le, fe_clear_env; rewrite PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold start; apply PTree.gss) HR) as [lef HLoop].
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (le2 := lef)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - apply fe_clear_entry.
  - rewrite fe_clear_body_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := start) (m1 := m).
    + apply exec_set. apply eval_Econst_int.
    + exact HLoop.
  - reflexivity.
  - reflexivity.
Qed.
Print Assumptions eval_fe_clear_from_stores.
