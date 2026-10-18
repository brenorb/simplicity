(** General bounds for the original writer's magnitude-larger-than-one input. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import C.jet_sx_expr C.jet_sx_zval C.jet_sx_zrep.
Require Import C.jet_secp_write_fe_numeric.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition wide_write_bounds n : Z * Z :=
  match n with O => (0, Int64.max_unsigned) | S _ => (0, 2 ^ 60) end.
Lemma wide_write_condition_checked bd base :
  zb wide_write_bounds (write_fe_condition bd base) = Some (0,1) /\
  isk KI (write_fe_condition bd base) = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma wide_write_true_bytes_checked bd base :
  Forall (fun x => zb wide_write_bounds x = Some (0,255) /\ isk KI x = true)
    (write_fe_true_bytes bd base).
Proof. repeat constructor; vm_compute; reflexivity. Qed.
Lemma wide_write_false_bytes_checked bd base :
  Forall (fun x => zb wide_write_bounds x = Some (0,255) /\ isk KI x = true)
    (write_fe_false_bytes bd base).
Proof. repeat constructor; vm_compute; reflexivity. Qed.
