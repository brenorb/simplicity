(** Exact real output words reconstructed for the existing scalar writer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_scalar_limb_bridge C.jet_secp_scalar_writer_run
  C.jet_secp_scalar_writer_storage.
Require Import C.jet_secp_scalar_mul512_accumulate.
Require Import C.jet_secp_scalar_mul_caller_alloc
  C.jet_secp_scalar_mul_caller_function C.jet_secp_scalar_mul_caller_observed.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma four_words_decompose (xs : list int64) : length xs = 4%nat ->
  xs = [nth 0 xs Int64.zero; nth 1 xs Int64.zero;
        nth 2 xs Int64.zero; nth 3 xs Int64.zero].
Proof.
  intro H; do 4 (destruct xs as [|? xs]; [discriminate|]).
  destruct xs; [reflexivity|cbn [length] in H; lia].
Qed.

Lemma four_words_scalar_limbs (xs : list int64) : length xs = 4%nat ->
  map Int64.repr (scalar_limbs_of (column_words_value xs)) = xs.
Proof.
  intro H. rewrite (four_words_decompose xs H).
  set (w0 := nth 0 xs Int64.zero); set (w1 := nth 1 xs Int64.zero).
  set (w2 := nth 2 xs Int64.zero); set (w3 := nth 3 xs Int64.zero).
  assert (HV : column_words_value [w0;w1;w2;w3] =
    Int64.unsigned w0 + 2 ^ 64 * Int64.unsigned w1 +
      2 ^ 128 * Int64.unsigned w2 + 2 ^ 192 * Int64.unsigned w3).
  { cbn [column_words_value]. change Int64.modulus with (2 ^ 64).
    assert (H2 : 2 ^ 128 = (2 ^ 64) ^ 2) by (vm_compute; reflexivity).
    assert (H3 : 2 ^ 192 = (2 ^ 64) ^ 3) by (vm_compute; reflexivity).
    rewrite H2,H3. ring. }
  rewrite HV,scalar_limbs_of_four_words. cbn [map].
  rewrite !Int64.repr_unsigned. reflexivity.
Qed.

Lemma four_words_scalar_at m b xs :
  length xs = 4%nat ->
  Mem.range_perm m b 0 32 Cur Freeable ->
  (forall i w, nth_error xs i = Some w ->
    Mem.load Mint64 m b (8 * Z.of_nat i) = Some (Vlong w)) ->
  scalar_at m b 0 (map Int64.repr (scalar_limbs_of (column_words_value xs))).
Proof.
  intros HL HP HV. rewrite four_words_scalar_limbs by exact HL.
  split; [exact HL|]. split; [lia|]. split; [exists 0; reflexivity|].
  split; [change (32 <= 18446744073709551615); lia|].
  split.
  - intros ofs HOfs; eapply Mem.perm_implies; [apply HP; exact HOfs|constructor].
  - intros i w Hn. rewrite Z.add_0_l. exact (HV i w Hn).
Qed.

Local Opaque scalar_mul_caller_output scalar_mul_caller_words.
Lemma scalar_mul_output_owned rho beta m :
  rep (C.jet_secp_product_reduce_bridge.product_reduce_rho rho)
    [lay beta 0] (scalar_mul_caller_output rho) m ->
  bas beta 0 = 0 /\ Mem.range_perm m (blk beta 0) 0 32 Cur Freeable.
Proof.
  intro HR.
  pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as HRegion.
  destruct HRegion as (_ & _ & _ & _ & HOwned).
  exact (conj (proj1 HOwned) (proj1 (proj2 (proj2 HOwned)))).
Qed.

Theorem scalar_writer_initial_rep_from_mul rho beta m :
  rep (C.jet_secp_product_reduce_bridge.product_reduce_rho rho)
    [lay beta 0] (scalar_mul_caller_output rho) m ->
  (forall i w, nth_error (scalar_mul_caller_words rho) i = Some w ->
    Mem.load Mint64 m (blk beta 0) (bas beta 0 + 8 * Z.of_nat i) = Some (Vlong w)) ->
  rep (scalar_limb_rho (column_words_value (scalar_mul_caller_words rho)))
    [(blk beta 0,bas beta 0)] scalar_writer_initial_regs m.
Proof.
  intros HR HV. destruct (scalar_mul_output_owned rho beta m HR) as (HB & HP).
  rewrite HB in HV |- *.
  apply scalar_writer_initial_rep_from_storage; [|exact HP].
  apply four_words_scalar_at; [apply scalar_mul_caller_word_count|exact HP|].
  intros i w Hn. specialize (HV i w Hn). rewrite Z.add_0_l in HV. exact HV.
Qed.
