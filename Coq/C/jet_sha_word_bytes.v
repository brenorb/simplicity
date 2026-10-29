(** Shared pure word/register/byte conversion proofs. These proof scripts
    come from jet_bitcoin_build_tapleaf_spec and jet_secp_generator_hash_literal.
    Keeping this foundation independent of their execution consumers permits
    reuse without importing the full SHA-context or SWU lifecycle. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_word_repr C.jet_buffer_input C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks
 C.jet_sha_ctx8_model C.jet_sha_be32_exec C.jet_sha_be32_write
 C.jet_secp_fe_math C.jet_secp_input_bytes C.jet_full_shift_spec C.jet_vector_shift_word.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma sha_word32_be_bytes (w : Ty.tySem (Word 5)) :
  c_be32_bytes (Int64.repr (Int.unsigned (word32_array_value w))) =
    map word8_array_value (word_bytes w).
Proof.
  destruct w as [[b0 b1] [b2 b3]].
  change (word_bytes (b0, b1, (b2, b3))) with [b0; b1; b2; b3]. cbn [map].
  pose proof (word_toZ_range 3 b0) as R0. pose proof (word_toZ_range 3 b1) as R1.
  pose proof (word_toZ_range 3 b2) as R2. pose proof (word_toZ_range 3 b3) as R3.
  change (2 ^ Z.of_nat (Nat.pow 2 3)) with 256 in R0, R1, R2, R3.
  set (t0 := @toZ (WordToZ 3) b0) in *. set (t1 := @toZ (WordToZ 3) b1) in *.
  set (t2 := @toZ (WordToZ 3) b2) in *. set (t3 := @toZ (WordToZ 3) b3) in *.
  assert (HT : @toZ (WordToZ 5) (b0, b1, (b2, b3)) = (t0 * 256 + t1) * 65536 + (t2 * 256 + t3))
    by reflexivity.
  set (W := (t0 * 256 + t1) * 65536 + (t2 * 256 + t3)) in *.
  assert (HWr : 0 <= W < 4294967296) by (unfold W; lia).
  change (word32_array_value (b0, b1, (b2, b3))) with (Int.repr W).
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  assert (HX : Int64.unsigned (Int64.repr W) = W)
    by (apply Int64.unsigned_repr; change Int64.max_unsigned with 18446744073709551615; lia).
  unfold c_be32_bytes.
  rewrite !zero_ext8_loword, !and255_unsigned.
  rewrite (shru64_unsigned (Int64.repr W) 24), (shru64_unsigned (Int64.repr W) 16),
    (shru64_unsigned (Int64.repr W) 8) by lia. rewrite HX.
  change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  assert (E3 : W / 16777216 = t0)
    by (symmetry; apply (Z.div_unique_pos W 16777216 t0 (t1 * 65536 + t2 * 256 + t3)); unfold W; lia).
  assert (E2 : W / 65536 = t0 * 256 + t1)
    by (symmetry; apply (Z.div_unique_pos W 65536 (t0 * 256 + t1) (t2 * 256 + t3)); unfold W; lia).
  assert (E1 : W / 256 = (t0 * 256 + t1) * 256 + t2)
    by (symmetry; apply (Z.div_unique_pos W 256 ((t0 * 256 + t1) * 256 + t2) t3); unfold W; lia).
  rewrite E3, E2, E1. rewrite !Z.mod_mod by lia.
  assert (M3 : t0 mod 256 = t0) by (apply Z.mod_small; lia).
  assert (M2 : (t0 * 256 + t1) mod 256 = t1)
    by (rewrite Z.add_comm, Z.mod_add by lia; apply Z.mod_small; lia).
  assert (M1 : ((t0 * 256 + t1) * 256 + t2) mod 256 = t2)
    by (rewrite Z.add_comm, Z.mod_add by lia; apply Z.mod_small; lia).
  assert (M0 : W mod 256 = t3).
  { unfold W. replace ((t0 * 256 + t1) * 65536 + (t2 * 256 + t3)) with
      (t3 + ((t0 * 256 + t1) * 256 + t2) * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite M3, M2, M1, M0. reflexivity.
Qed.

Lemma sha_words_be_bytes (ws : list (Ty.tySem (Word 5))) :
  be_bytes (map word32_array_value ws) = map word8_array_value (flat_map word_bytes ws).
Proof.
  induction ws as [|w ws IH]; [reflexivity|].
  unfold be_bytes in *. cbn [map flat_map]. rewrite map_app, IH, sha_word32_be_bytes. reflexivity.
Qed.

Lemma sha_state_be_bytes (h : Ty.tySem (Word 8)) :
  be_bytes (state_regs h) = map word8_array_value (vector_values (Word 3) 5 h).
Proof. unfold state_regs. rewrite sha_words_be_bytes. reflexivity. Qed.

Lemma word_bytes_integer_app left right :
  be_val (left++right)=be_val left*256^Z.of_nat (length right)+be_val right.
Proof. unfold be_val at 1;rewrite fold_left_app;apply fold_be_linear. Qed.

Lemma vector_bytes_integer n (w:Ty.tySem (Vector (Word 3) n)) :
  be_val (map Int.unsigned (map word8_array_value (vector_values (Word 3) n w)))=
    vector_value (WordToZ 3) n w.
Proof.
  revert w;induction n as [|n IH];intro w.
  - change (Int.unsigned (Int.repr (@toZ (WordToZ 3) w))=@toZ (WordToZ 3) w).
    apply Int.unsigned_repr;pose proof (word_toZ_range 3 w) as Bound.
    change (0<=@toZ (WordToZ 3) w<256) in Bound.
    change Int.max_unsigned with 4294967295;lia.
  - destruct w as [hi lo].
    change (be_val (map Int.unsigned (map word8_array_value
      (vector_values (Word 3) n hi++vector_values (Word 3) n lo)))=
      vector_value (WordToZ 3) n hi*two_power_nat (vector_bits (WordToZ 3) n)+
      vector_value (WordToZ 3) n lo).
    rewrite !map_app,word_bytes_integer_app,!map_length,vector_values_length,!IH.
    rewrite vector_word_bits,two_power_nat_equiv,word_bitSize.
    replace (Nat.pow 2 (n+3)) with (8*Nat.pow 2 n)%nat by
      (rewrite Nat.pow_add_r;cbn;lia).
    rewrite Nat2Z.inj_mul,Z.pow_mul_r by lia;reflexivity.
Qed.

Lemma word256_bytes_integer (w:Ty.tySem (Word 8)) :
  be_val (map Int.unsigned (map word8_array_value (vector_values (Word 3) 5 w)))=
    @toZ (WordToZ 8) w.
Proof.
  rewrite vector_bytes_integer.
  pose proof (vector_word_value 3 5 w) as Value.
  change (@toZ (WordToZ 8) w=vector_value (WordToZ 3) 5 w) in Value.
  symmetry;exact Value.
Qed.

Lemma sha_state_bytes_integer h :
 be_val (map Int.unsigned (C.jet_sha_be32_write.be_bytes (state_regs h)))=@toZ (WordToZ 8) h.
Proof. rewrite sha_state_be_bytes;apply word256_bytes_integer. Qed.
