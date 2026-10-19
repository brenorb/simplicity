(** Proof-producing equality reflection for closed symbolic output checks. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Values AST Ctypes Coqlib.
Require Import C.jet_sx_expr.
Set Default Timeout 10.
Definition bop_eq_dec (a b : bop) : {a=b}+{a<>b}.
Proof. decide equality. Defined.
Definition shop_eq_dec (a b : shop) : {a=b}+{a<>b}.
Proof. decide equality. Defined.
Definition comparison_eq_dec (a b : comparison) : {a=b}+{a<>b}.
Proof. decide equality. Defined.
Definition signedness_eq_dec (a b : signedness) : {a=b}+{a<>b}.
Proof. decide equality. Defined.
Definition decision_bool {A} (dec : forall a b : A, {a=b}+{a<>b}) a b :=
  if dec a b then true else false.
Lemma decision_bool_sound A dec (a b : A) : decision_bool dec a b = true -> a = b.
Proof. unfold decision_bool; destruct (dec a b); congruence. Qed.

(** This recognizer is intentionally partial: unsupported syntax returns
    false. Soundness suffices, and the concrete source check must return true. *)
Fixpoint sx_same a b := match a,b with
  | XIc a, XIc b => Int.eq a b
  | XL a, XL b | XLc a, XLc b => Int64.eq a b
  | XLv a, XLv b => Nat.eqb a b
  | XLb op a b, XLb op' a' b' =>
      decision_bool bop_eq_dec op op' && sx_same a a' && sx_same b b'
  | XLsh op a k, XLsh op' a' k' =>
      decision_bool shop_eq_dec op op' && sx_same a a' && Z.eqb k k'
  | XLcmp c sg a b, XLcmp c' sg' a' b' =>
      decision_bool comparison_eq_dec c c' && decision_bool signedness_eq_dec sg sg'
        && sx_same a a' && sx_same b b'
  | XI2L sg a, XI2L sg' a' => decision_bool signedness_eq_dec sg sg' && sx_same a a'
  | XL2I a, XL2I b => sx_same a b
  | _,_ => false
  end.
Lemma sx_same_sound a : forall b, sx_same a b = true -> a = b.
Proof.
  induction a; destruct b; cbn [sx_same]; intro H; try discriminate.
  all: repeat match goal with
    | H : andb _ _ = true |- _ => apply Bool.andb_true_iff in H; destruct H
    end.
  all: f_equal; eauto using Int.same_if_eq, Int64.same_if_eq,
    Nat.eqb_eq, Z.eqb_eq, decision_bool_sound.
  all: first [apply Nat.eqb_eq; assumption | apply Z.eqb_eq; assumption].
Qed.
