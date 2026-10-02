(** Complete actual rotate_{16,32,64} scalar helper calls.
    The zero branch is essential: it avoids shifting by the full carrier width.
    These are helper contracts, not canonical jet-equivalence results. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_wide.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_rotate_helper s := match s with
  W16 => f_rotate_16 | W32 => f_rotate_32 | W64 => f_rotate_64 end.
Definition wide_rotate_expr s := Ecast
  (Ebinop Oor
    (Ebinop Oshl (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _value tulong) tulong)
      (Etempvar _amt tuchar) tulong)
    (Ebinop Oshr (Etempvar _value tulong)
      (Ebinop Osub (Econst_int (Int.repr (wide_bits s)) tint) (Etempvar _amt tuchar) tint) tulong) tulong) tulong.
Definition wide_rotate_nonzero s r a :=
  Int64.or (Int64.shl r (Int64.repr (Int.unsigned a)))
    (Int64.shru r (Int64.repr (wide_bits s - Int.unsigned a))).
Definition wide_rotate_result s r a := if Int.eq a Int.zero then r else wide_rotate_nonzero s r a.
Definition le_wide_rotate r a : temp_env :=
  PTree.set _amt (Vint a) (PTree.set _value (Vlong r) (PTree.empty val)).

Lemma wide_rotate_helper_body s : (wide_rotate_helper s).(fn_body) =
  Sifthenelse (Etempvar _amt tuchar)
    (Sreturn (Some (wide_rotate_expr s))) (Sreturn (Some (Etempvar _value tulong))).
Proof. destruct s; reflexivity. Qed.

Lemma long_int_shift_guard a :
  0 <= Int.unsigned a < 64 -> Int.ltu a Int64.iwordsize' = Datatypes.true.
Proof.
  intros HA. unfold Int.ltu.
  change ((if zlt (Int.unsigned a) 64 then Datatypes.true else Datatypes.false) = Datatypes.true).
  rewrite zlt_true by lia; reflexivity.
Qed.

Lemma eval_wide_rotate_expr s e le m r a :
  0 < Int.unsigned a < wide_bits s ->
  le!_value = Some (Vlong r) -> le!_amt = Some (Vint a) ->
  eval_expr ge0 e le m (wide_rotate_expr s) (Vlong (wide_rotate_nonzero s r a)).
Proof.
  intros HA HV HM. pose proof (wide_bits_bounds s) as Hwidth.
  assert (HG : Int.ltu a Int64.iwordsize' = Datatypes.true) by (apply long_int_shift_guard; lia).
  assert (Hrange : 0 <= wide_bits s - Int.unsigned a <= Int.max_unsigned).
  { change Int.max_unsigned with 4294967295; lia. }
  assert (HS : Int.sub (Int.repr (wide_bits s)) a = Int.repr (wide_bits s - Int.unsigned a)).
  { unfold Int.sub. rewrite Int.unsigned_repr; [reflexivity|].
    change Int.max_unsigned with 4294967295; lia. }
  assert (HRG : Int.ltu (Int.repr (wide_bits s - Int.unsigned a)) Int64.iwordsize' = Datatypes.true).
  { apply long_int_shift_guard. rewrite Int.unsigned_repr by exact Hrange; lia. }
  unfold wide_rotate_expr, wide_rotate_nonzero.
  eapply eval_Ecast with (v1 := Vlong
    (Int64.or (Int64.shl r (Int64.repr (Int.unsigned a)))
      (Int64.shru r (Int64.repr (wide_bits s - Int.unsigned a))))).
  - eapply eval_Ebinop with
      (v1 := Vlong (Int64.shl r (Int64.repr (Int.unsigned a))))
      (v2 := Vlong (Int64.shru r (Int64.repr (wide_bits s - Int.unsigned a)))).
    + eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vint a).
      * eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong r).
        -- constructor.
        -- apply eval_Etempvar; exact HV.
        -- change (Some (Vlong (Int64.mul Int64.one r)) = Some (Vlong r)).
           rewrite Int64.mul_commut, Int64.mul_one; reflexivity.
      * apply eval_Etempvar; exact HM.
      * change ((if Int.ltu a Int64.iwordsize' then
          Some (Vlong (Int64.shl r (Int64.repr (Int.unsigned a)))) else None) =
          Some (Vlong (Int64.shl r (Int64.repr (Int.unsigned a))))).
        rewrite HG; reflexivity.
    + eapply eval_Ebinop with (v1 := Vlong r)
        (v2 := Vint (Int.repr (wide_bits s - Int.unsigned a))).
      * apply eval_Etempvar; exact HV.
      * eapply eval_Ebinop with (v1 := Vint (Int.repr (wide_bits s))) (v2 := Vint a).
        -- constructor.
        -- apply eval_Etempvar; exact HM.
        -- change (Some (Vint (Int.sub (Int.repr (wide_bits s)) a)) =
            Some (Vint (Int.repr (wide_bits s - Int.unsigned a)))). rewrite HS; reflexivity.
      * change ((if Int.ltu (Int.repr (wide_bits s - Int.unsigned a)) Int64.iwordsize'
          then Some (Vlong (Int64.shru r (Int64.repr (Int.unsigned (Int.repr (wide_bits s - Int.unsigned a))))))
          else None) = Some (Vlong (Int64.shru r (Int64.repr (wide_bits s - Int.unsigned a))))).
        rewrite HRG, Int.unsigned_repr by exact Hrange; reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma entry_wide_rotate s m r a :
  function_entry2 ge0 (wide_rotate_helper s) [Vlong r; Vint a]
    m empty_env (le_wide_rotate r a) m.
Proof.
  constructor.
  - destruct s; constructor.
  - destruct s; change (list_norepet [_value; _amt]); repeat constructor; cbn; intuition discriminate.
  - destruct s; change (list_disjoint [_value; _amt] []); intros id1 id2 H1 H2 Heq; contradiction.
  - destruct s; constructor.
  - destruct s; reflexivity.
Qed.

Theorem eval_wide_rotate_helper s m r a :
  0 <= Int.unsigned a < wide_bits s ->
  Clight2.eval_funcall ge0 m (Internal (wide_rotate_helper s)) [Vlong r; Vint a]
    E0 m (Vlong (wide_rotate_result s r a)).
Proof.
  intros HA.
  eapply eval_funcall_internal with (e := empty_env) (le1 := le_wide_rotate r a)
    (le2 := le_wide_rotate r a) (m1 := m) (m2 := m)
    (out := Out_return (Some (Vlong (wide_rotate_result s r a), tulong))).
  - apply entry_wide_rotate.
  - rewrite wide_rotate_helper_body.
    eapply exec_Sifthenelse with (v1 := Vint a) (b := negb (Int.eq a Int.zero)).
    + apply eval_Etempvar. unfold le_wide_rotate; apply PTree.gss.
    + reflexivity.
    + unfold wide_rotate_result. destruct (Int.eq a Int.zero) eqn:HZ; cbn [negb].
      * apply exec_Sreturn_some. apply eval_Etempvar.
        unfold le_wide_rotate. rewrite PTree.gso by discriminate; apply PTree.gss.
      * apply exec_Sreturn_some. apply eval_wide_rotate_expr.
        -- assert (HN : Int.unsigned a <> 0).
           { intro H0. assert (HE : a = Int.zero).
             { rewrite <- (Int.repr_unsigned a), H0; reflexivity. }
             subst a; discriminate. }
           lia.
        -- unfold le_wide_rotate. rewrite PTree.gso by discriminate; apply PTree.gss.
        -- unfold le_wide_rotate; apply PTree.gss.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - destruct s; reflexivity.
Qed.
