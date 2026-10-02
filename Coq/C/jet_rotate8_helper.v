(** Actual rotate_8 scalar helper: unsigned left-shift promotion and signed
    right-shift promotion, followed by the uchar truncation. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_rotate_count_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rotate8_expr := Ecast
  (Ebinop Oor
    (Ebinop Oshl (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _value tuchar) tuint)
      (Etempvar _amt tuchar) tuint)
    (Ebinop Oshr (Etempvar _value tuchar)
      (Ebinop Osub (Econst_int (Int.repr 8) tint) (Etempvar _amt tuchar) tint) tint) tuint) tuchar.
Definition rotate8_nonzero r a := Int.zero_ext 8
  (Int.or (Int.shl r a) (Int.shr r (Int.repr (8 - Int.unsigned a)))).
Definition rotate8_result r a := if Int.eq a Int.zero then r else rotate8_nonzero r a.
Definition le_rotate8 r a := PTree.set _amt (Vint a) (PTree.set _value (Vint r) (PTree.empty val)).

Lemma rotate8_body : f_rotate_8.(fn_body) =
  Sifthenelse (Etempvar _amt tuchar) (Sreturn (Some rotate8_expr))
    (Sreturn (Some (Etempvar _value tuchar))).
Proof. reflexivity. Qed.

Lemma int_shift_guard a : 0 <= Int.unsigned a < 32 -> Int.ltu a Int.iwordsize = true.
Proof.
  intros HA. unfold Int.ltu. change ((if zlt (Int.unsigned a) 32 then true else false) = true).
  rewrite zlt_true by lia. reflexivity.
Qed.

Lemma eval_rotate8_expr e le m r a :
  0 < Int.unsigned a < 8 -> le!_value = Some (Vint r) -> le!_amt = Some (Vint a) ->
  eval_expr ge0 e le m rotate8_expr (Vint (rotate8_nonzero r a)).
Proof.
  intros HA HV HM.
  assert (HG : Int.ltu a Int.iwordsize = true) by (apply int_shift_guard; lia).
  assert (HC : 0 <= 8 - Int.unsigned a <= Int.max_unsigned).
  { change Int.max_unsigned with 4294967295; lia. }
  assert (HS : Int.sub (Int.repr 8) a = Int.repr (8 - Int.unsigned a)).
  { unfold Int.sub. change (Int.unsigned (Int.repr 8)) with 8. reflexivity. }
  assert (HRG : Int.ltu (Int.repr (8 - Int.unsigned a)) Int.iwordsize = true).
  { apply int_shift_guard. rewrite Int.unsigned_repr by exact HC; lia. }
  unfold rotate8_expr, rotate8_nonzero.
  eapply eval_Ecast with (v1 := Vint (Int.or (Int.shl r a) (Int.shr r (Int.repr (8 - Int.unsigned a))))).
  - eapply eval_Ebinop with (v1 := Vint (Int.shl r a))
      (v2 := Vint (Int.shr r (Int.repr (8 - Int.unsigned a)))).
    + eapply eval_Ebinop with (v1 := Vint r) (v2 := Vint a).
      * eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vint r).
        -- constructor.
        -- apply eval_Etempvar; exact HV.
        -- change (Some (Vint (Int.mul Int.one r)) = Some (Vint r)).
           rewrite Int.mul_commut, Int.mul_one; reflexivity.
      * apply eval_Etempvar; exact HM.
      * change ((if Int.ltu a Int.iwordsize then Some (Vint (Int.shl r a)) else None) =
          Some (Vint (Int.shl r a))). rewrite HG; reflexivity.
    + eapply eval_Ebinop with (v1 := Vint r) (v2 := Vint (Int.repr (8 - Int.unsigned a))).
      * apply eval_Etempvar; exact HV.
      * eapply eval_Ebinop with (v1 := Vint (Int.repr 8)) (v2 := Vint a).
        -- constructor.
        -- apply eval_Etempvar; exact HM.
        -- change (Some (Vint (Int.sub (Int.repr 8) a)) = Some (Vint (Int.repr (8 - Int.unsigned a)))).
           rewrite HS; reflexivity.
      * change ((if Int.ltu (Int.repr (8 - Int.unsigned a)) Int.iwordsize
          then Some (Vint (Int.shr r (Int.repr (8 - Int.unsigned a)))) else None) =
          Some (Vint (Int.shr r (Int.repr (8 - Int.unsigned a))))). rewrite HRG; reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma entry_rotate8 m r a : function_entry2 ge0 f_rotate_8 [Vint r; Vint a]
  m empty_env (le_rotate8 r a) m.
Proof.
  constructor.
  - constructor.
  - change (list_norepet [_value; _amt]); repeat constructor; cbn; intuition discriminate.
  - intros id1 id2 H1 H2 Heq; contradiction.
  - constructor.
  - reflexivity.
Qed.

Theorem eval_rotate8_helper m r a : 0 <= Int.unsigned r < 256 -> 0 <= Int.unsigned a < 8 ->
  Clight2.eval_funcall ge0 m (Internal f_rotate_8) [Vint r; Vint a] E0 m (Vint (rotate8_result r a)).
Proof.
  intros HR HA.
  eapply eval_funcall_internal with (e := empty_env) (le1 := le_rotate8 r a) (le2 := le_rotate8 r a)
    (m1 := m) (m2 := m) (out := Out_return (Some (Vint (rotate8_result r a), tuchar))).
  - apply entry_rotate8.
  - rewrite rotate8_body. eapply exec_Sifthenelse with (v1 := Vint a) (b := negb (Int.eq a Int.zero)).
    + apply eval_Etempvar. unfold le_rotate8; apply PTree.gss.
    + reflexivity.
    + unfold rotate8_result. destruct (Int.eq a Int.zero) eqn:HZ; cbn [negb].
      * apply exec_Sreturn_some. apply eval_Etempvar. unfold le_rotate8; rewrite PTree.gso by discriminate; apply PTree.gss.
      * pose proof (Int.eq_spec a Int.zero) as HN. rewrite HZ in HN.
        assert (HP : 0 < Int.unsigned a).
        { assert (Int.unsigned a <> 0).
          { intro HE. apply HN. rewrite <- (Int.repr_unsigned a), HE. reflexivity. } lia. }
        apply exec_Sreturn_some. apply eval_rotate8_expr; [lia| |].
        -- unfold le_rotate8; rewrite PTree.gso by discriminate; apply PTree.gss.
        -- unfold le_rotate8; apply PTree.gss.
  - cbn; split; [discriminate|].
    change (Some (Vint (Int.zero_ext 8 (rotate8_result r a))) = Some (Vint (rotate8_result r a))).
    unfold rotate8_result. destruct (Int.eq a Int.zero).
    + rewrite byte_carrier_cast_id by exact HR; reflexivity.
    + unfold rotate8_nonzero. rewrite Int.zero_ext_idem by lia; reflexivity.
  - reflexivity.
Qed.
