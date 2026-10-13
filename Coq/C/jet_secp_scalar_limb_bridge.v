(** Exact little-endian limbs recovered from their weighted value. This
    bridges actual reader storage to the serializer's existing representation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Memory Values.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_local_regions C.jet_secp_wrapper_run C.jet_secp_input_bytes C.jet_input_layout.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_scalar_reader_value C.jet_secp_scalar_reader_lifecycle.
Require Import C.jet_secp_scalar_overflow_numeric C.jet_secp_canonical_scalar.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma radix_four_limbs base a0 a1 a2 a3 :
  0 < base ->
  0 <= a0 < base -> 0 <= a1 < base -> 0 <= a2 < base -> 0 <= a3 < base ->
  let value := a0 + base * a1 + base ^ 2 * a2 + base ^ 3 * a3 in
  value mod base = a0 /\ (value / base) mod base = a1 /\
  (value / base ^ 2) mod base = a2 /\ value / base ^ 3 = a3.
Proof.
  intros HB H0 H1 H2 H3; cbn zeta.
  assert (HL2 : 0 <= a0 + base * a1 < base ^ 2) by nia.
  assert (HL3 : 0 <= a0 + base * a1 + base ^ 2 * a2 < base ^ 3) by nia.
  assert (HE0 : a0 + base * a1 + base ^ 2 * a2 + base ^ 3 * a3 =
    a0 + (a1 + base * a2 + base ^ 2 * a3) * base) by ring.
  assert (HE1 : a1 + base * a2 + base ^ 2 * a3 = a1 + (a2 + base * a3) * base) by ring.
  assert (HE2 : a0 + base * a1 + base ^ 2 * a2 + base ^ 3 * a3 =
    (a0 + base * a1) + (a2 + base * a3) * base ^ 2) by ring.
  assert (HE3 : a0 + base * a1 + base ^ 2 * a2 + base ^ 3 * a3 =
    (a0 + base * a1 + base ^ 2 * a2) + a3 * base ^ 3) by ring.
  split.
  - rewrite HE0, Z.mod_add by lia. apply Z.mod_small; exact H0.
  - split.
    + rewrite HE0, Z.div_add by lia. rewrite Z.div_small by exact H0.
      rewrite Z.add_0_l, HE1, Z.mod_add by lia. apply Z.mod_small; exact H1.
    + split.
      * rewrite HE2, Z.div_add by nia. rewrite Z.div_small by exact HL2.
        rewrite Z.add_0_l.
        replace (a2 + base * a3) with (a2 + a3 * base) by ring.
        rewrite Z.mod_add by lia. apply Z.mod_small; exact H2.
      * rewrite HE3, Z.div_add by nia. rewrite Z.div_small by exact HL3.
        apply Z.add_0_l.
Qed.

Lemma scalar_limbs_of_four_words w0 w1 w2 w3 :
  scalar_limbs_of
    (Int64.unsigned w0 + 2 ^ 64 * Int64.unsigned w1 +
     2 ^ 128 * Int64.unsigned w2 + 2 ^ 192 * Int64.unsigned w3) =
    [Int64.unsigned w0; Int64.unsigned w1; Int64.unsigned w2; Int64.unsigned w3].
Proof.
  assert (HP2 : (2 ^ 64) ^ 2 = 2 ^ 128) by (vm_compute; reflexivity).
  assert (HP3 : (2 ^ 64) ^ 3 = 2 ^ 192) by (vm_compute; reflexivity).
  pose proof (radix_four_limbs (2 ^ 64) (Int64.unsigned w0) (Int64.unsigned w1)
    (Int64.unsigned w2) (Int64.unsigned w3) ltac:(lia)
    (Int64.unsigned_range w0) (Int64.unsigned_range w1)
    (Int64.unsigned_range w2) (Int64.unsigned_range w3)) as HLimbs.
  rewrite HP2, HP3 in HLimbs.
  destruct HLimbs as [H0 [H1 [H2 H3]]].
  unfold scalar_limbs_of; rewrite H0, H1, H2, H3; reflexivity.
Qed.

Lemma scalar_reader_limbs_canonical value rc layout :
  map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8)
    (@canonical_scalar_normalize Alg.CoreFunSem value))) =
  [scalar_reader_limb (read_fe_rho (frame_input_word_bits value) rc) layout 0;
   scalar_reader_limb (read_fe_rho (frame_input_word_bits value) rc) layout 1;
   scalar_reader_limb (read_fe_rho (frame_input_word_bits value) rc) layout 2;
   scalar_reader_limb (read_fe_rho (frame_input_word_bits value) rc) layout 3].
Proof.
  assert (HValue : scalar_limb_value (scalar_reader_limb
    (read_fe_rho (frame_input_word_bits value) rc) layout) =
    @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)).
  { rewrite scalar_reader_value_mod_group by (rewrite frame_input_word_bits_length; reflexivity).
    rewrite input_bytes_word256_value, canonical_scalar_normalize_numeric; reflexivity. }
  rewrite <- HValue.
  unfold scalar_limb_value.
  rewrite scalar_limbs_of_four_words; cbn [map]; rewrite !Int64.repr_unsigned; reflexivity.
Qed.

Lemma scalar_reader_storage_for_serializer value rc layout bi edge m :
  rep (read_fe_rho (frame_input_word_bits value) rc) layout
    (scalar_reader_final_regs bi edge) m ->
  scalar_at m (blk layout 0) (bas layout 0)
    (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8)
      (@canonical_scalar_normalize Alg.CoreFunSem value)))) /\
  Mem.range_perm m (blk layout 0) 0 32 Cur Freeable.
Proof.
  intro HRep.
  pose proof (scalar_reader_final_loads _ _ _ _ _ HRep) as HLoads.
  assert (HOwned : bas layout 0 = 0 /\ Mem.range_perm m (blk layout 0) 0 32 Cur Freeable).
  { eapply rep_free_region; [exact HRep|rewrite scalar_reader_final_length; lia|].
    unfold scalar_reader_final_regs.
    rewrite C.jet_secp_scalar_reader_set.scalar_reader_set_regions; reflexivity. }
  destruct HOwned as [HBase HFree].
  split; [|exact HFree]. unfold scalar_at.
  split; [cbn [scalar_limbs_of length map]; reflexivity|].
  split; [lia|]. split; [rewrite HBase; exists 0; lia|].
  split; [rewrite HBase; change (32 <= 18446744073709551615); lia|].
  split.
  - intros pos HPos; eapply Mem.perm_implies; [apply HFree; lia|constructor].
  - intros i limb HNth.
    rewrite (scalar_reader_limbs_canonical value rc (lay layout)) in HNth.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error] in HNth.
    all: try (inversion HNth; subst limb; apply HLoads; lia).
    destruct i; discriminate.
Qed.
