(** Exact numeric value of the original native field-storage packer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import C.jet_secp_storage_pack C.jet_secp_storage_numeric
 C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_u128_word_shift
 C.jet_secp_multiply_input_input C.jet_secp_b32_exec
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma storage_shl_unsigned w k : 0<=k<64 ->
 Int64.unsigned (Int64.shl w (Int64.repr k))=(Int64.unsigned w mod 2^(64-k))*2^k.
Proof.
 intro K;rewrite Int64.shl_mul_two_p.
 rewrite Int64.unsigned_repr by (change Int64.max_unsigned with (2^64-1);lia).
 rewrite two_p_equiv;unfold Int64.mul;rewrite Int64.unsigned_repr_eq.
 rewrite Int64.unsigned_repr.
 2:{ change Int64.max_unsigned with (2^64-1).
     assert (0<2^k) by (apply Z.pow_pos_nonneg;lia).
     assert (2^k<=2^63) by (apply Z.pow_le_mono_r;lia);lia. }
 change Int64.modulus with (2^64).
 replace (2^64) with (2^(64-k)*2^k)
  by (rewrite <-Z.pow_add_r by lia;f_equal;lia).
 apply Z.mul_mod_distr_r;apply Z.pow_nonzero;lia.
Qed.
Lemma storage_pack_join_unsigned a b k : 0<=k<64 ->
 Int64.unsigned a<2^k ->
 Int64.unsigned (Int64.or a (Int64.shl b (Int64.repr k)))=
 Int64.unsigned a+(Int64.unsigned b mod 2^(64-k))*2^k.
Proof.
 intros K A;unfold Int64.or;rewrite storage_shl_unsigned by exact K.
 pose proof (Int64.unsigned_range a) as AR.
 pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as P.
 pose proof (Z.mod_pos_bound (Int64.unsigned b) (2^(64-k))
  ltac:(apply Z.pow_pos_nonneg;lia)) as B.
 rewrite lor_shift_add by lia.
 apply Int64.unsigned_repr;change Int64.max_unsigned with (2^64-1).
 replace (2^64) with (2^(64-k)*2^k)
  by (rewrite <-Z.pow_add_r by lia;f_equal;lia).
 nia.
Qed.
Lemma storage_pack_numeric w :
 fe_limbs_ok (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
 (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) ->
 field_storage_value (storage_pack_words w)=radix_value w.
Proof.
 intros (B0 & B1 & B2 & B3 & B4).
 unfold field_storage_value,storage_pack_words;cbn [List.nth].
 rewrite !storage_pack_join_unsigned.
 2-9: try lia;try (rewrite uns_shru by lia;apply Z.div_lt_upper_bound;lia).
 rewrite !uns_shru by lia.
 replace (Int64.unsigned (w 4%nat) mod 2^(64-16)) with (Int64.unsigned (w 4%nat))
  by (symmetry;apply Z.mod_small;lia).
 rewrite radix_value_matches_normalizer;unfold fe_val.
 pose proof (Z.div_mod (Int64.unsigned (w 1%nat)) (2^12) ltac:(lia)).
 pose proof (Z.div_mod (Int64.unsigned (w 2%nat)) (2^24) ltac:(lia)).
 pose proof (Z.div_mod (Int64.unsigned (w 3%nat)) (2^36) ltac:(lia)).
 change (64-52) with 12;change (64-40) with 24;change (64-28) with 36.
 lia.
Qed.
Theorem storage_pack_canonical value : 0<=value<2^256 ->
 field_storage_value (storage_pack_words (limb_rho value))=value.
Proof.
 intro V;rewrite storage_pack_numeric.
 - apply radix_limb_rho;exact V.
 - rewrite !limb_rho_unsigned by exact V;exact (proj1 (fe_limbs_of_ok value V)).
Qed.
