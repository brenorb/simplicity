(** Representation bridge between the actual context reader counter and the
    context writer's quotient/remainder operations. Not public jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word C.jet_read_sha256_counter C.jet_buffer_chunks.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma sha256_counter_shift_constant :
  two_p (Int64.unsigned (Int64.repr 6)) = 64.
Proof. vm_compute; reflexivity. Qed.

Lemma sha256_counter_unsigned count len :
  Int64.unsigned count < 36028797018963968 ->
  Int64.unsigned len < 64 ->
  Int64.unsigned (sha256_read_counter count len) =
    64 * Int64.unsigned count + Int64.unsigned len.
Proof.
  intros HC HL.
  pose proof (Int64.unsigned_range count) as HCount.
  pose proof (Int64.unsigned_range len) as HLen.
  assert (HMax : Int64.max_unsigned = 18446744073709551615) by reflexivity.
  unfold sha256_read_counter.
  change (Int64.unsigned (Int64.add
    (Int64.shl (Int64.mul count Int64.one) (Int64.repr 6)) len) =
      64 * Int64.unsigned count + Int64.unsigned len).
  rewrite Int64.mul_one, Int64.shl_mul_two_p, sha256_counter_shift_constant.
  unfold Int64.mul.
  rewrite (Int64.unsigned_repr 64) by (rewrite HMax; lia).
  rewrite Int64.add_unsigned.
  rewrite (Int64.unsigned_repr (Int64.unsigned count * 64)) by (rewrite HMax; nia).
  rewrite Int64.unsigned_repr by (rewrite HMax; nia).
  ring.
Qed.

Lemma sha256_counter_remainder count len :
  Int64.unsigned count < 36028797018963968 ->
  Int64.unsigned len < 64 ->
  Int64.modu (sha256_read_counter count len) (Int64.repr 64) = len.
Proof.
  intros HC HL. unfold Int64.modu.
  rewrite sha256_counter_unsigned by assumption.
  assert (HU : Int64.unsigned (Int64.repr 64) = 64) by reflexivity.
  rewrite HU.
  replace (64 * Int64.unsigned count + Int64.unsigned len) with
    (Int64.unsigned len + Int64.unsigned count * 64) by ring.
  rewrite Z.mod_add by lia.
  rewrite Z.mod_small by (pose proof (Int64.unsigned_range len); lia).
  apply Int64.repr_unsigned.
Qed.

Lemma sha256_counter_quotient count len :
  Int64.unsigned count < 36028797018963968 ->
  Int64.unsigned len < 64 ->
  Int64.shru (sha256_read_counter count len) (Int64.repr 6) = count.
Proof.
  intros HC HL. rewrite Int64.shru_div_two_p, sha256_counter_shift_constant.
  rewrite sha256_counter_unsigned by assumption.
  replace (64 * Int64.unsigned count + Int64.unsigned len) with
    (Int64.unsigned count * 64 + Int64.unsigned len) by ring.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small by (pose proof (Int64.unsigned_range len); lia).
  rewrite Z.add_0_r. apply Int64.repr_unsigned.
Qed.

Lemma sha256_buffer63_length_range (buf : Ty.tySem (buffer_type (Word 3) 5)) :
  0 <= Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf))) < 64.
Proof.
  pose proof (byte_chunks_values_bound _ (buffer_byte_chunks_sized 5 buf)) as HB.
  rewrite buffer63_chunks_capacity in HB. lia.
Qed.

Lemma sha256_counter_buffer63_representation count
    (buf : Ty.tySem (buffer_type (Word 3) 5)) :
  Int64.unsigned count < 36028797018963968 ->
  let len := Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf))) in
  Int64.unsigned (sha256_read_counter count (Int64.repr len)) =
    64 * Int64.unsigned count + len /\
  Int64.modu (sha256_read_counter count (Int64.repr len)) (Int64.repr 64) = Int64.repr len /\
  Int64.shru (sha256_read_counter count (Int64.repr len)) (Int64.repr 6) = count.
Proof.
  intro HC. cbn zeta.
  pose proof (sha256_buffer63_length_range buf) as HL.
  assert (HU : Int64.unsigned (Int64.repr
    (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf))))) =
      Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf)))).
  { apply Int64.unsigned_repr.
    change (0 <= Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf))) <= 18446744073709551615); lia. }
  split.
  - rewrite sha256_counter_unsigned; [rewrite HU; reflexivity|exact HC|rewrite HU; lia].
  - split; [apply sha256_counter_remainder|apply sha256_counter_quotient];
      [exact HC|rewrite HU; lia|exact HC|rewrite HU; lia].
Qed.
