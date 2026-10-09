(** Numeric representation bridge for the actual C field-add outputs.
    This is not a replacement for the literal canonical jet program. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_fe_math C.jet_secp_field_add_values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition field_input_value (rho : nat -> int64) (start : nat) : Z :=
  fe_val (Int64.unsigned (rho start))
    (Int64.unsigned (rho ((start + 1)%nat)))
    (Int64.unsigned (rho ((start + 2)%nat)))
    (Int64.unsigned (rho ((start + 3)%nat)))
    (Int64.unsigned (rho ((start + 4)%nat))).

Lemma field_add_values_sum rho :
  (forall n, (n < 5)%nat ->
    Int64.unsigned (rho (S n)) <= 2 ^ 52 - 1 /\
    Int64.unsigned (rho ((6 + n)%nat)) <= 2 ^ 52 - 1) ->
  fe_val (Int64.unsigned (add_value rho 0))
    (Int64.unsigned (add_value rho 1)) (Int64.unsigned (add_value rho 2))
    (Int64.unsigned (add_value rho 3)) (Int64.unsigned (add_value rho 4)) =
    field_input_value rho 1 + field_input_value rho 6.
Proof.
  intro H.
  assert (HU : forall n, (n < 5)%nat ->
    Int64.unsigned (add_value rho n) =
      Int64.unsigned (rho (S n)) + Int64.unsigned (rho ((6 + n)%nat))).
  { intros n Hn. destruct (H n Hn) as [HA HB].
    apply add_value_unsigned; assumption. }
  unfold field_input_value, fe_val.
  rewrite (HU 0%nat ltac:(lia)), (HU 1%nat ltac:(lia)), (HU 2%nat ltac:(lia)),
    (HU 3%nat ltac:(lia)), (HU 4%nat ltac:(lia)).
  cbn [Nat.add]. ring.
Qed.
Print Assumptions field_add_values_sum.
