(** Complete original SWU helper on every raw Word256 limb representation.
    In particular, a rejected set_b32 digest is still executed, with the low
    bit actually stored by C. This does not assert public acceptance of it. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.extraMath C.jet_word_repr C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_fe_math C.jet_secp_b32_exec C.jet_secp_square_columns C.jet_secp_square_spec_bridge
  C.jet_secp_multiply_input_input C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_root_chain_numeric C.jet_secp_swu_startup C.jet_secp_swu_function
  C.jet_secp_swu_word_parity C.jet_secp_field_odd_words C.jet_secp_swu_parity
  C.jet_secp_swu_literal C.jet_secp_swu_literal_bridge C.jet_secp_rescale_literal
  C.jet_secp_canonical_odd C.jet_secp_canonical_normalize C.jet_secp_gej_negate_literal C.jet_clight_internal_preserve.
Require Import C.jet_secp_input_bytes.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_swu rescale_field_output swu_selected_candidate literal_ge_negate
  canonical_fe_normalize canonical_fe_is_odd.

Definition swu_raw_words (t:Ty.tySem (Word 8)) := limb_rho (@toZ (WordToZ 8) t).
Lemma swu_raw_matches t : root_words_match (swu_raw_words t) t.
Proof.
  split.
  - intros i Index;pose proof (limb_rho_bound (@toZ (WordToZ 8) t) (word_toZ_range 8 t) i) as Bound.
    change (0<=Int64.unsigned (swu_raw_words t i)<=4503599627370495) in Bound.
    destruct (Nat.eqb i 4);lia.
  - unfold swu_raw_words;rewrite radix_limb_rho by apply word_toZ_range;reflexivity.
Qed.

Definition swu_digest_word bytes := @fromZ (WordToZ 8) (be_val bytes).
Lemma swu_digest_value bytes : length bytes=32%nat -> Forall (fun x=>0<=x<=255) bytes ->
  @toZ (WordToZ 8) (swu_digest_word bytes)=be_val bytes.
Proof.
  intros Len Bytes;unfold swu_digest_word;rewrite to_fromZ,two_power_nat_equiv,word_bitSize.
  change (be_val bytes mod 2^256=be_val bytes);apply Z.mod_small;apply be_32_bytes_bound;assumption.
Qed.
Lemma swu_digest_input bytes m bi : length bytes=32%nat -> Forall (fun x=>0<=x<=255) bytes ->
  fe_at m bi 0 (map Int64.repr (fe_limbs_of (be_val bytes))) ->
  fe_at m bi 0 (words5 (swu_raw_words (swu_digest_word bytes))).
Proof.
  intros Len Bytes Input;unfold swu_raw_words;rewrite swu_digest_value by assumption;exact Input.
Qed.
Lemma swu_raw_odd t : field_words_odd (swu_raw_words t)=Z.testbit (@toZ (WordToZ 8) t) 0.
Proof.
  unfold field_words_odd,swu_raw_words.
  change (Z.testbit (Int64.unsigned (Int64.repr (@toZ (WordToZ 8) t mod 2^52))) 0=
    Z.testbit (@toZ (WordToZ 8) t) 0).
  rewrite Int64.unsigned_repr by
    (pose proof (Z.mod_pos_bound (@toZ (WordToZ 8) t) (2^52) ltac:(lia));
      change Int64.max_unsigned with 18446744073709551615;lia).
  apply Z.mod_pow2_bits_low;lia.
Qed.
Lemma swu_raw_accepted_output t : @toZ (WordToZ 8) t<feP ->
  swu_words_literal_output (swu_raw_words t) t=@literal_swu Alg.CoreFunSem t.
Proof.
  intro Accepted;unfold swu_words_literal_output;rewrite swu_raw_odd,swu_literal_selected_step.
  assert (Odd:swu_input_odd t=Z.testbit (@toZ (WordToZ 8) t) 0).
  { unfold swu_input_odd;rewrite canonical_fe_is_odd_numeric,canonical_fe_normalize_numeric,
      canonical_field_order_matches_limb_model.
    rewrite Z.mod_small by (pose proof (word_toZ_range 8 t);lia);reflexivity. }
  unfold swu_input_odd in Odd;rewrite Odd;reflexivity.
Qed.

Theorem eval_swu_raw_function t m bp bi :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  bp<>bi -> swu_startup m -> fe_at m bi 0 (words5 (swu_raw_words t)) ->
  Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m bp 0 88 Cur Freeable ->
  exists mf x y,
  Clight2.eval_funcall secp_ge m (Internal f_shallue_van_de_woestijne)
    [Vptr bp Ptrofs.zero;Vptr bi Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\
  Mem.load Mint32 mf bp 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bi 0 40 Cur Freeable /\ Mem.range_perm mf bp 0 88 Cur Freeable /\
  square_input_bounds x /\ square_input_bounds y /\
  (rescale_field_output x,rescale_field_output y)=swu_words_literal_output (swu_raw_words t) t /\
  swu_startup mf /\ lframe (fun b _=>b<>bp /\ b<>bi) m mf /\ readonly_preserved m mf.
Proof.
  intros Count Separate Ready Input FI FP.
  exact (eval_swu_function_words (swu_raw_words t) t m bp bi Count Separate Ready (swu_raw_matches t) Input FI FP).
Qed.
