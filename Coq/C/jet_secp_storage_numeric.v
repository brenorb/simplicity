(** Exact unsigned value of the original 4x64 to 5x52 storage decoder. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import C.jet_secp_storage_unpack C.jet_secp_signed62_numeric
 C.jet_secp_fe_math C.jet_secp_fe_b32 C.jet_secp_u128_word_shift C.jet_secp_multiply_finish_product
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_multiply_normalize_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma storage_masked_shift_unsigned x shift width :
 0<=shift<=width -> width<64 ->
 Int64.unsigned (Int64.and (Int64.shl x (Int64.repr shift))
   (Int64.repr (2^width-1)))=(Int64.unsigned x mod 2^(width-shift))*2^shift.
Proof.
 intros HS HW;rewrite repack_mask_unsigned by lia.
 rewrite Int64.shl_mul_two_p.
 rewrite Int64.unsigned_repr by (change Int64.max_unsigned with (2^64-1);lia).
 rewrite two_p_equiv.
 unfold Int64.mul;rewrite Int64.unsigned_repr_eq.
 change Int64.modulus with (2^64).
 rewrite Int64.unsigned_repr.
 2: { split;[apply Z.pow_nonneg;lia|].
      change Int64.max_unsigned with (2^64-1).
      assert (2^shift<=2^63) by (apply Z.pow_le_mono_r;lia);lia. }
 rewrite mod_mod_pow by lia.
 replace (2^width) with (2^(width-shift)*2^shift)
   by (rewrite <-Z.pow_add_r by lia;f_equal;lia).
 apply Z.mul_mod_distr_r;apply Z.pow_nonzero;lia.
Qed.

Lemma storage_join_unsigned a b drop shift :
 0<drop<64 -> 0<=shift<=52 -> drop+shift=64 ->
 Int64.unsigned (Int64.or (Int64.shru a (Int64.repr drop))
   (Int64.and (Int64.shl b (Int64.repr shift)) (Int64.repr (2^52-1))))=
 Int64.unsigned a/2^drop+(Int64.unsigned b mod 2^(52-shift))*2^shift.
Proof.
 intros HD HS Sum;unfold Int64.or.
 rewrite uns_shru by lia;rewrite storage_masked_shift_unsigned by lia.
 pose proof (Int64.unsigned_range a) as RA.
 change Int64.modulus with (2^64) in RA.
 assert (Lo : 0<=Int64.unsigned a/2^drop<2^shift).
 { split;[apply Z.div_pos;[lia|apply Z.pow_pos_nonneg;lia]|].
   apply Z.div_lt_upper_bound;[apply Z.pow_pos_nonneg;lia|].
   rewrite <-Z.pow_add_r by lia;rewrite Sum;lia. }
 pose proof (Z.mod_pos_bound (Int64.unsigned b) (2^(52-shift))
   ltac:(apply Z.pow_pos_nonneg;lia)) as Hi.
 rewrite lor_shift_add by lia.
 apply Int64.unsigned_repr.
 split;[nia|].
 change Int64.max_unsigned with (2^64-1).
 assert (Bound : Int64.unsigned a/2^drop+
   (Int64.unsigned b mod 2^(52-shift))*2^shift<2^52).
 { replace (2^52) with (2^(52-shift)*2^shift)
     by (rewrite <-Z.pow_add_r by lia;f_equal;lia).
   assert (0<2^shift) by (apply Z.pow_pos_nonneg;lia);nia. }
 lia.
Qed.

Definition storage_unpack_value (w : nat->int64) i := nth i
 [Int64.unsigned (w 0%nat) mod 2^52;
  Int64.unsigned (w 0%nat)/2^52+(Int64.unsigned (w 1%nat) mod 2^40)*2^12;
  Int64.unsigned (w 1%nat)/2^40+(Int64.unsigned (w 2%nat) mod 2^28)*2^24;
  Int64.unsigned (w 2%nat)/2^28+(Int64.unsigned (w 3%nat) mod 2^16)*2^36;
  Int64.unsigned (w 3%nat)/2^16] 0.

Lemma storage_unpack_words_numeric w i : (i<5)%nat ->
 Int64.unsigned (storage_unpack_words w i)=storage_unpack_value w i.
Proof.
 intro HI;destruct i as [|[|[|[|[|i]]]]];try lia;
 cbn [storage_unpack_words storage_unpack_value nth].
 - apply repack_mask_unsigned;lia.
 - apply storage_join_unsigned;lia.
 - apply storage_join_unsigned;lia.
 - apply storage_join_unsigned;lia.
 - apply uns_shru;lia.
Qed.

Definition field_storage_value (w : nat->int64) :=
 Int64.unsigned (w 0%nat)+2^64*Int64.unsigned (w 1%nat)+
 2^128*Int64.unsigned (w 2%nat)+2^192*Int64.unsigned (w 3%nat).

Theorem storage_unpack_preserves_value w :
 radix_value (storage_unpack_words w)=field_storage_value w.
Proof.
 rewrite radix_value_matches_normalizer;unfold fe_val.
 rewrite !storage_unpack_words_numeric by lia.
 unfold storage_unpack_value,field_storage_value;cbn [nth].
 pose proof (Z.div_mod (Int64.unsigned (w 0%nat)) (2^52) ltac:(lia)).
 pose proof (Z.div_mod (Int64.unsigned (w 1%nat)) (2^40) ltac:(lia)).
 pose proof (Z.div_mod (Int64.unsigned (w 2%nat)) (2^28) ltac:(lia)).
 pose proof (Z.div_mod (Int64.unsigned (w 3%nat)) (2^16) ltac:(lia)).
 lia.
Qed.

Theorem storage_unpack_limb_bounds w :
 fe_limbs_ok (Int64.unsigned (storage_unpack_words w 0%nat))
   (Int64.unsigned (storage_unpack_words w 1%nat))
   (Int64.unsigned (storage_unpack_words w 2%nat))
   (Int64.unsigned (storage_unpack_words w 3%nat))
   (Int64.unsigned (storage_unpack_words w 4%nat)).
Proof.
 rewrite !storage_unpack_words_numeric by lia.
 unfold storage_unpack_value,fe_limbs_ok;cbn [nth].
 pose proof (Int64.unsigned_range (w 0%nat)) as R0.
 pose proof (Int64.unsigned_range (w 1%nat)) as R1.
 pose proof (Int64.unsigned_range (w 2%nat)) as R2.
 pose proof (Int64.unsigned_range (w 3%nat)) as R3.
 change Int64.modulus with (2^64) in R0,R1,R2,R3.
 pose proof (Z.mod_pos_bound (Int64.unsigned (w 0%nat)) (2^52) ltac:(lia)).
 pose proof (Z.mod_pos_bound (Int64.unsigned (w 1%nat)) (2^40) ltac:(lia)).
 pose proof (Z.mod_pos_bound (Int64.unsigned (w 2%nat)) (2^28) ltac:(lia)).
 pose proof (Z.mod_pos_bound (Int64.unsigned (w 3%nat)) (2^16) ltac:(lia)).
 assert (D0 : 0<=Int64.unsigned (w 0%nat)/2^52<2^12)
   by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
 assert (D1 : 0<=Int64.unsigned (w 1%nat)/2^40<2^24)
   by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
 assert (D2 : 0<=Int64.unsigned (w 2%nat)/2^28<2^36)
   by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
 assert (D3 : 0<=Int64.unsigned (w 3%nat)/2^16<2^48)
   by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
 repeat split;lia.
Qed.

Theorem storage_unpack_exact_limbs w :
 map Int64.unsigned (words5 (storage_unpack_words w))=fe_limbs_of (field_storage_value w).
Proof.
 unfold words5;cbn [map];apply fe_limbs_unique.
 - exact (storage_unpack_limb_bounds w).
 - rewrite <-radix_value_matches_normalizer;apply storage_unpack_preserves_value.
Qed.

Theorem storage_unpack_normalized w :
 normalized_words (storage_unpack_words w)=fe_limbs_of (field_storage_value w mod feP).
Proof.
 rewrite bounded_normalized_words.
 - rewrite storage_unpack_preserves_value;reflexivity.
 - intros i HI;pose proof (storage_unpack_limb_bounds w) as B.
   destruct B as (B0 & B1 & B2 & B3 & B4).
   destruct i as [|[|[|[|[|i]]]]];lia.
Qed.
