(** Build the actual helper's initial representation from two owned fields. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory AST.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_field_add.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition field_values (rho : nat -> int64) (start : nat) : list int64 :=
  [rho start; rho ((start + 1)%nat); rho ((start + 2)%nat);
   rho ((start + 3)%nat); rho ((start + 4)%nat)].

Lemma field_region_from_values rho start layout m r :
  fe_at m (blk layout r) (bas layout r) (field_values rho start) ->
  region_ok rho layout m r (fe_reg (vars5 start)).
Proof.
  intros (HBase & HAlign & HMax & HPerm & HLoad).
  apply region_u64.
  - exact HBase.
  - exact HAlign.
  - change (bas layout r + 40 <= Ptrofs.max_unsigned); exact HMax.
  - eapply Mem.perm_valid_block; apply (HPerm (bas layout r)); lia.
  - change (Mem.range_perm m (blk layout r) (bas layout r) (bas layout r + 40) Cur Writable).
    exact HPerm.
  - intros i x HNth.
    destruct i as [|i]; [inversion HNth; subst x; split; [exact (HLoad 0%nat _ eq_refl)|reflexivity]|].
    destruct i as [|i]; [inversion HNth; subst x; split; [exact (HLoad 1%nat _ eq_refl)|reflexivity]|].
    destruct i as [|i]; [inversion HNth; subst x; split; [exact (HLoad 2%nat _ eq_refl)|reflexivity]|].
    destruct i as [|i]; [inversion HNth; subst x; split; [exact (HLoad 3%nat _ eq_refl)|reflexivity]|].
    destruct i as [|i]; [inversion HNth; subst x; split; [exact (HLoad 4%nat _ eq_refl)|reflexivity]|].
    destruct i; discriminate.
Qed.

Lemma field_region_storage_size start :
  Forall (fun c => cofs c + size_chunk (cchunk c) <= 40)
    (rcells (fe_reg (vars5 start))).
Proof. repeat constructor; cbn; lia. Qed.

Theorem field_add_initial_from_owned_fields m a b rho :
  a <> b ->
  fe_at m a 0 (field_values rho 1) -> fe_at m b 0 (field_values rho 6) ->
  Mem.range_perm m a 0 40 Cur Freeable -> Mem.range_perm m b 0 40 Cur Freeable ->
  rep rho [(a,0);(b,0)] field_add_initial_regs m.
Proof.
  intros HSeparate HA HB HFreeA HFreeB.
  unfold field_add_initial_regs.
  apply (rep_add rho [(a,0)] [free_region (fe_reg (vars5 1)) 40] m b 0).
  - apply (rep_add rho [] [] m a 0); [apply rep_nil|cbn; tauto|].
    apply region_with_freeable.
    + apply field_region_from_values; exact HA.
    + reflexivity.
    + reflexivity.
    + exact HFreeA.
    + apply field_region_storage_size.
  - cbn. intros [HEqual|HFalse]; [congruence|contradiction].
  - apply region_with_freeable.
    + apply field_region_from_values; exact HB.
    + reflexivity.
    + reflexivity.
    + exact HFreeB.
    + apply field_region_storage_size.
Qed.
Print Assumptions field_add_initial_from_owned_fields.
