(** Table of the libsecp256k1 functions of the secp256k1 translation unit,
    for symbolic execution. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight Globalenvs.
Require Import C.jet_sx_exec C.jet_sx_pure C.jets_secp C.jet_secp_linkage.
Import ListNotations.
Set Default Timeout 1500.

Definition secp_pure : list (ident * function) :=
  [ (_secp256k1_ctz64_var, f_secp256k1_ctz64_var);
    (_secp256k1_umul128, f_secp256k1_umul128);
    (_secp256k1_mul128, f_secp256k1_mul128);
    (_secp256k1_u128_mul, f_secp256k1_u128_mul);
    (_secp256k1_u128_accum_mul, f_secp256k1_u128_accum_mul);
    (_secp256k1_u128_accum_u64, f_secp256k1_u128_accum_u64);
    (_secp256k1_u128_rshift, f_secp256k1_u128_rshift);
    (_secp256k1_u128_to_u64, f_secp256k1_u128_to_u64);
    (_secp256k1_u128_hi_u64, f_secp256k1_u128_hi_u64);
    (_secp256k1_u128_from_u64, f_secp256k1_u128_from_u64);
    (_secp256k1_i128_mul, f_secp256k1_i128_mul);
    (_secp256k1_i128_accum_mul, f_secp256k1_i128_accum_mul);
    (_secp256k1_i128_rshift, f_secp256k1_i128_rshift);
    (_secp256k1_i128_to_u64, f_secp256k1_i128_to_u64);
    (_secp256k1_i128_to_i64, f_secp256k1_i128_to_i64);
    (_secp256k1_modinv64_signed62_assign, f_secp256k1_modinv64_signed62_assign);
    (_secp256k1_modinv64_normalize_62, f_secp256k1_modinv64_normalize_62);
    (_secp256k1_modinv64_divsteps_62_var, f_secp256k1_modinv64_divsteps_62_var);
    (_secp256k1_modinv64_update_de_62, f_secp256k1_modinv64_update_de_62);
    (_secp256k1_modinv64_update_fg_62_var, f_secp256k1_modinv64_update_fg_62_var);
    (_secp256k1_modinv64_var, f_secp256k1_modinv64_var);
    (_secp256k1_fe_mul_inner, f_secp256k1_fe_mul_inner);
    (_secp256k1_fe_sqr_inner, f_secp256k1_fe_sqr_inner);
    (_secp256k1_fe_normalize_weak, f_secp256k1_fe_normalize_weak);
    (_secp256k1_fe_normalize_var, f_secp256k1_fe_normalize_var);
    (_secp256k1_fe_normalizes_to_zero_var, f_secp256k1_fe_normalizes_to_zero_var);
    (_secp256k1_fe_set_int, f_secp256k1_fe_set_int);
    (_secp256k1_fe_is_zero, f_secp256k1_fe_is_zero);
    (_secp256k1_fe_is_odd, f_secp256k1_fe_is_odd);
    (_secp256k1_fe_clear, f_secp256k1_fe_clear);
    (_secp256k1_fe_set_b32, f_secp256k1_fe_set_b32);
    (_secp256k1_fe_get_b32, f_secp256k1_fe_get_b32);
    (_secp256k1_fe_negate, f_secp256k1_fe_negate);
    (_secp256k1_fe_mul_int, f_secp256k1_fe_mul_int);
    (_secp256k1_fe_add_int, f_secp256k1_fe_add_int);
    (_secp256k1_fe_add, f_secp256k1_fe_add);
    (_secp256k1_fe_mul, f_secp256k1_fe_mul);
    (_secp256k1_fe_sqr, f_secp256k1_fe_sqr);
    (_secp256k1_fe_cmov, f_secp256k1_fe_cmov);
    (_secp256k1_fe_half, f_secp256k1_fe_half);
    (_secp256k1_fe_to_storage, f_secp256k1_fe_to_storage);
    (_secp256k1_fe_from_storage, f_secp256k1_fe_from_storage);
    (_secp256k1_fe_from_signed62, f_secp256k1_fe_from_signed62);
    (_secp256k1_fe_to_signed62, f_secp256k1_fe_to_signed62);
    (_secp256k1_fe_inv_var, f_secp256k1_fe_inv_var);
    (_secp256k1_fe_equal_var, f_secp256k1_fe_equal_var);
    (_secp256k1_fe_sqrt_var, f_secp256k1_fe_sqrt_var);
    (_secp256k1_scalar_set_int, f_secp256k1_scalar_set_int);
    (_secp256k1_scalar_get_bits, f_secp256k1_scalar_get_bits);
    (_secp256k1_scalar_get_bits_var, f_secp256k1_scalar_get_bits_var);
    (_secp256k1_scalar_check_overflow, f_secp256k1_scalar_check_overflow);
    (_secp256k1_scalar_reduce, f_secp256k1_scalar_reduce);
    (_secp256k1_scalar_add, f_secp256k1_scalar_add);
    (_secp256k1_scalar_cadd_bit, f_secp256k1_scalar_cadd_bit);
    (_secp256k1_scalar_set_b32, f_secp256k1_scalar_set_b32);
    (_secp256k1_scalar_get_b32, f_secp256k1_scalar_get_b32);
    (_secp256k1_scalar_is_zero, f_secp256k1_scalar_is_zero);
    (_secp256k1_scalar_negate, f_secp256k1_scalar_negate);
    (_secp256k1_scalar_reduce_512, f_secp256k1_scalar_reduce_512);
    (_secp256k1_scalar_mul_512, f_secp256k1_scalar_mul_512);
    (_secp256k1_scalar_mul, f_secp256k1_scalar_mul);
    (_secp256k1_scalar_split_128, f_secp256k1_scalar_split_128);
    (_secp256k1_scalar_mul_shift_var, f_secp256k1_scalar_mul_shift_var);
    (_secp256k1_scalar_from_signed62, f_secp256k1_scalar_from_signed62);
    (_secp256k1_scalar_to_signed62, f_secp256k1_scalar_to_signed62);
    (_secp256k1_scalar_inverse_var, f_secp256k1_scalar_inverse_var);
    (_secp256k1_scalar_split_lambda, f_secp256k1_scalar_split_lambda);
    (_secp256k1_ge_set_gej_zinv, f_secp256k1_ge_set_gej_zinv);
    (_secp256k1_ge_set_xy, f_secp256k1_ge_set_xy);
    (_secp256k1_ge_is_infinity, f_secp256k1_ge_is_infinity);
    (_secp256k1_ge_neg, f_secp256k1_ge_neg);
    (_secp256k1_ge_set_gej_var, f_secp256k1_ge_set_gej_var);
    (_secp256k1_ge_table_set_globalz, f_secp256k1_ge_table_set_globalz);
    (_secp256k1_gej_set_infinity, f_secp256k1_gej_set_infinity);
    (_secp256k1_ge_set_infinity, f_secp256k1_ge_set_infinity);
    (_secp256k1_ge_set_xo_var, f_secp256k1_ge_set_xo_var);
    (_secp256k1_gej_set_ge, f_secp256k1_gej_set_ge);
    (_secp256k1_gej_eq_var, f_secp256k1_gej_eq_var);
    (_secp256k1_gej_eq_ge_var, f_secp256k1_gej_eq_ge_var);
    (_secp256k1_gej_eq_x_var, f_secp256k1_gej_eq_x_var);
    (_secp256k1_gej_neg, f_secp256k1_gej_neg);
    (_secp256k1_gej_is_infinity, f_secp256k1_gej_is_infinity);
    (_secp256k1_ge_is_valid_var, f_secp256k1_ge_is_valid_var);
    (_secp256k1_gej_double, f_secp256k1_gej_double);
    (_secp256k1_gej_double_var, f_secp256k1_gej_double_var);
    (_secp256k1_gej_add_var, f_secp256k1_gej_add_var);
    (_secp256k1_gej_add_ge_var, f_secp256k1_gej_add_ge_var);
    (_secp256k1_gej_add_zinv_var, f_secp256k1_gej_add_zinv_var);
    (_secp256k1_gej_rescale, f_secp256k1_gej_rescale);
    (_secp256k1_ge_to_storage, f_secp256k1_ge_to_storage);
    (_secp256k1_ge_from_storage, f_secp256k1_ge_from_storage);
    (_secp256k1_ge_is_in_correct_subgroup, f_secp256k1_ge_is_in_correct_subgroup);
    (_secp256k1_ecmult_odd_multiples_table, f_secp256k1_ecmult_odd_multiples_table);
    (_secp256k1_ecmult_table_get_ge, f_secp256k1_ecmult_table_get_ge);
    (_secp256k1_ecmult_table_get_ge_lambda, f_secp256k1_ecmult_table_get_ge_lambda);
    (_secp256k1_ecmult_table_get_ge_storage, f_secp256k1_ecmult_table_get_ge_storage);
    (_secp256k1_ecmult_wnaf, f_secp256k1_ecmult_wnaf);
    (_secp256k1_ecmult_strauss_wnaf, f_secp256k1_ecmult_strauss_wnaf);
    (_secp256k1_ecmult, f_secp256k1_ecmult);
    (_secp256k1_eckey_pubkey_tweak_add, f_secp256k1_eckey_pubkey_tweak_add);
    (_secp256k1_pubkey_load, f_secp256k1_pubkey_load);
    (_secp256k1_pubkey_save, f_secp256k1_pubkey_save);
    (_secp256k1_ec_pubkey_tweak_add_helper, f_secp256k1_ec_pubkey_tweak_add_helper);
    (_secp256k1_xonly_pubkey_load, f_secp256k1_xonly_pubkey_load);
    (_secp256k1_xonly_pubkey_save, f_secp256k1_xonly_pubkey_save);
    (_secp256k1_xonly_pubkey_parse, f_secp256k1_xonly_pubkey_parse);
    (_secp256k1_xonly_pubkey_serialize, f_secp256k1_xonly_pubkey_serialize);
    (_secp256k1_extrakeys_ge_even_y, f_secp256k1_extrakeys_ge_even_y);
    (_secp256k1_xonly_pubkey_from_pubkey, f_secp256k1_xonly_pubkey_from_pubkey);
    (_secp256k1_xonly_pubkey_tweak_add, f_secp256k1_xonly_pubkey_tweak_add);
    (_secp256k1_schnorrsig_sha256_tagged, f_secp256k1_schnorrsig_sha256_tagged);
    (_secp256k1_schnorrsig_challenge, f_secp256k1_schnorrsig_challenge);
    (_secp256k1_schnorrsig_verify, f_secp256k1_schnorrsig_verify);
    (_secp256k1_generator_load, f_secp256k1_generator_load);
    (_secp256k1_generator_save, f_secp256k1_generator_save);
    (_secp256k1_generator_generate_internal, f_secp256k1_generator_generate_internal);
    (_secp256k1_generator_generate, f_secp256k1_generator_generate) ].

Lemma secp_pure_lookup :
  map (symbol_lookup secp_ge) secp_pure = map (fun p => Some (Internal (snd p))) secp_pure.
Proof. vm_cast_no_check (eq_refl (map (fun p => Some (Internal (snd p))) secp_pure)). Qed.

Lemma secp_pure_ok : forall id f, In (id, f) secp_pure ->
  exists b, Genv.find_symbol secp_ge id = Some b /\ Genv.find_funct_ptr secp_ge b = Some (Internal f).
Proof. exact (symbol_lookup_table secp_ge secp_pure secp_pure_lookup). Qed.

