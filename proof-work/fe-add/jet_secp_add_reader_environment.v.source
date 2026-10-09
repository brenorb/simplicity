(** Combine both normalized reader limb lists into the actual add helper's
    variable layout. No execution or output premise is hidden in this map. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_b32_exec C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_fe_math C.jet_secp_field_add_initial.
Require Import C.jet_secp_field_add_numeric C.jet_secp_negate_after_read.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition add_reader_rho (va vb : Z) (n : nat) : int64 :=
  if (n <? 6)%nat then limb_rho va ((n - 1)%nat)
  else limb_rho vb ((n - 6)%nat).

Lemma add_reader_rho_first va vb n : (n < 5)%nat ->
  add_reader_rho va vb (S n) = limb_rho va n.
Proof.
  intro H. do 5 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma add_reader_rho_second va vb n : (n < 5)%nat ->
  add_reader_rho va vb ((6 + n)%nat) = limb_rho vb n.
Proof.
  intro H. do 5 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma add_reader_field_first va vb :
  field_values (add_reader_rho va vb) 1 = map Int64.repr (fe_limbs_of va).
Proof. reflexivity. Qed.

Lemma add_reader_field_second va vb :
  field_values (add_reader_rho va vb) 6 = map Int64.repr (fe_limbs_of vb).
Proof. reflexivity. Qed.

Lemma add_reader_values va vb :
  0 <= va < 2 ^ 256 -> 0 <= vb < 2 ^ 256 ->
  field_input_value (add_reader_rho va vb) 1 = va /\
  field_input_value (add_reader_rho va vb) 6 = vb.
Proof.
  intros HA HB.
  destruct (field_rho_facts va 0 HA) as [_ HVA].
  destruct (field_rho_facts vb 0 HB) as [_ HVB].
  split; [exact HVA|exact HVB].
Qed.

Lemma add_reader_bounds va vb :
  0 <= va < 2 ^ 256 -> 0 <= vb < 2 ^ 256 ->
  forall n, (n < 5)%nat ->
    Int64.unsigned (add_reader_rho va vb (S n)) <= 2 ^ 52 - 1 /\
    Int64.unsigned (add_reader_rho va vb ((6 + n)%nat)) <= 2 ^ 52 - 1.
Proof.
  intros HA HB n Hn.
  rewrite add_reader_rho_first, add_reader_rho_second by exact Hn.
  split.
  - exact (proj2 (write_rho_bounds va 0 HA (S n))).
  - exact (proj2 (write_rho_bounds vb 0 HB (S n))).
Qed.
Print Assumptions add_reader_values.
Print Assumptions add_reader_bounds.
