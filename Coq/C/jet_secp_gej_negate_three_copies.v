(** Three original self-copy statements, derived from real point ownership. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_gej_negate_fields.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_gej_negate_three_self_copies le m b base :
  0 <= base -> (8 | base) -> base + 128 <= Ptrofs.max_unsigned ->
  le!_r = Some (Vptr b (Ptrofs.repr base)) ->
  le!_a = Some (Vptr b (Ptrofs.repr base)) ->
  Mem.range_perm m b base (base+128) Cur Freeable ->
  exists mx my mz,
    Clight2.exec_stmt secp_ge empty_env le m
      (gej_negate_field_copy_stmt _x) E0 le mx Out_normal /\
    Clight2.exec_stmt secp_ge empty_env le mx
      (gej_negate_field_copy_stmt _y) E0 le my Out_normal /\
    Clight2.exec_stmt secp_ge empty_env le my
      (gej_negate_field_copy_stmt _z) E0 le mz Out_normal /\
    Mem.unchanged_on (fun _ _ => True) m mz /\
    Mem.range_perm mz b base (base+128) Cur Freeable.
Proof.
  intros HB HA HM HR HS HP.
  destruct (exec_gej_negate_self_field_owned le m b base _x 0
    ltac:(left;reflexivity) HB HA HM HR HS HP) as (mx & HX & HFX & HPX).
  destruct (exec_gej_negate_self_field_owned le mx b base _y 40
    ltac:(right;left;reflexivity) HB HA HM HR HS HPX) as (my & HY & HFY & HPY).
  destruct (exec_gej_negate_self_field_owned le my b base _z 80
    ltac:(right;right;left;reflexivity) HB HA HM HR HS HPY) as (mz & HZ & HFZ & HPZ).
  exists mx,my,mz; split; [exact HX|]. split; [exact HY|].
  split; [exact HZ|]. split; [|exact HPZ].
  eapply Mem.unchanged_on_trans; [exact HFX|].
  eapply Mem.unchanged_on_trans; eassumption.
Qed.
Timeout 60 Print Assumptions exec_gej_negate_three_self_copies.
