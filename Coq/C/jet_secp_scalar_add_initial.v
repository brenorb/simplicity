(** Construct the real add helper representation from two distinct owned
    32-byte scalars. No helper execution or output is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_local_regions C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_scalar_add_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_add_vars (start : nat) :=
  [XLv start; XLv (start+1)%nat; XLv (start+2)%nat; XLv (start+3)%nat].
Definition scalar_add_values (rho : nat -> int64) (start : nat) :=
  [rho start; rho (start+1)%nat; rho (start+2)%nat; rho (start+3)%nat].

Lemma scalar_add_vars_nth start i x :
  nth_error (scalar_add_vars start) i = Some x ->
  (i < 4)%nat /\ x = XLv (start+i)%nat.
Proof.
  unfold scalar_add_vars; destruct i as [|[|[|[|i]]]]; cbn [nth_error]; intro H;
    try (inversion H; subst x; split; [lia|f_equal; lia]).
  destruct i; discriminate.
Qed.

Lemma scalar_add_region_from_values rho start layout m r :
  bas layout r = 0 ->
  scalar_at m (blk layout r) (bas layout r) (scalar_add_values rho start) ->
  Mem.range_perm m (blk layout r) 0 32 Cur Freeable ->
  region_ok rho layout m r (mkreg (u64_cells 0 (scalar_add_vars start)) true (Some 32)).
Proof.
  intros HZero (HLength & HBase & HAlign & HMax & HPerm & HLoad) HFree.
  change (region_ok rho layout m r
    (free_region (mkreg (u64_cells 0 (scalar_add_vars start)) true None) 32)).
  apply region_with_freeable.
  - apply region_u64.
    + exact HBase.
    + exact HAlign.
    + exact HMax.
    + eapply Mem.perm_valid_block; apply (HFree 0); lia.
    + rewrite HZero; cbn; apply freeable_range_writable; exact HFree.
    + intros i x HNth.
      destruct (scalar_add_vars_nth start i x HNth) as [HIndex ->].
      split; [|reflexivity].
      change (Mem.load Mint64 m (blk layout r) (bas layout r + 8 * Z.of_nat i) =
        Some (Vlong (rho (start+i)%nat))).
      apply HLoad; unfold scalar_add_values.
      destruct i as [|[|[|[|i]]]]; try lia; cbn [nth_error];
        f_equal; f_equal; lia.
  - exact HZero.
  - reflexivity.
  - exact HFree.
  - unfold scalar_add_vars; repeat constructor; cbn; lia.
Qed.

Theorem scalar_add_initial_from_owned_scalars m a b rho :
  a <> b ->
  scalar_at m a 0 (scalar_add_values rho 0) ->
  scalar_at m b 0 (scalar_add_values rho 4) ->
  Mem.range_perm m a 0 32 Cur Freeable ->
  Mem.range_perm m b 0 32 Cur Freeable ->
  rep rho [(a,0);(b,0)] scalar_add_initial_regs m.
Proof.
  intros HSeparate HA HB HFreeA HFreeB.
  change (rep rho [(a,0);(b,0)]
    [mkreg (u64_cells 0 (scalar_add_vars 0)) true (Some 32);
     mkreg (u64_cells 0 (scalar_add_vars 4)) true (Some 32)] m).
  apply (rep_add rho [(a,0)] [mkreg (u64_cells 0 (scalar_add_vars 0)) true (Some 32)] m b 0).
  - apply (rep_add rho [] [] m a 0); [apply rep_nil|cbn; tauto|].
    apply scalar_add_region_from_values; [reflexivity|exact HA|exact HFreeA].
  - cbn; intros [HEqual|HFalse]; [congruence|contradiction].
  - apply scalar_add_region_from_values; [reflexivity|exact HB|exact HFreeB].
Qed.
