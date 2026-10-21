(** Actual C half and multiply-three/half outputs against the fixed literal
    Simplicity programs. Input agreement is modulo p, not canonical storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Word Simplicity.Alg Simplicity.Ty.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math C.jet_secp_fe_nv
  C.jet_secp_square_columns C.jet_secp_field_half C.jet_secp_field_half_numeric
  C.jet_secp_field_mul_small C.jet_secp_double_l_scale C.jet_secp_double_literal
  C.jet_secp_double_half_literal_numeric C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_halve literal_fe_multiply_int secp_ge half_words mul_small_words.

Lemma field_double_cancel_mod a b : (2*a) mod feP=(2*b) mod feP -> a mod feP=b mod feP.
Proof.
  intro HE;pose proof double_half_constant as [_ HC].
  assert (HP : feP<>0) by (unfold feP,feR;lia).
  assert (HM : (((feP+1)/2)*(2*a)) mod feP=(((feP+1)/2)*(2*b)) mod feP).
  { rewrite <-(Z.mul_mod_idemp_r ((feP+1)/2) (2*a) feP) by exact HP.
    rewrite <-(Z.mul_mod_idemp_r ((feP+1)/2) (2*b) feP) by exact HP.
    rewrite HE;reflexivity. }
  assert (HA : forall v, ((feP+1)/2)*(2*v)=v+v*feP).
  { intro v;replace (((feP+1)/2)*(2*v)) with ((2*((feP+1)/2))*v) by ring.
    rewrite HC;ring. }
  rewrite !HA in HM;rewrite !Z.mod_add in HM by exact HP;exact HM.
Qed.

Theorem half_words_matches_literal w (a : Ty.tySem (Word 8)) :
  square_input_bounds w -> radix_value w mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value (half_words w) mod feP=@toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem a).
Proof.
  intros HB HI.
  transitivity (@toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem a) mod feP).
  - apply field_double_cancel_mod;rewrite half_value_identity by exact HB.
    rewrite Z.mod_add by (unfold feP,feR;lia).
    rewrite literal_fe_halve_double;exact HI.
  - apply Z.mod_small;apply literal_fe_halve_range.
Qed.

Theorem eval_field_half_literal w (a : Ty.tySem (Word 8)) m b :
  square_input_bounds w -> fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable ->
  radix_value w mod feP=@toZ (WordToZ 8) a mod feP ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_half) [Vptr b Ptrofs.zero] E0 mf Vundef /\
  fe_at mf b 0 (words5 (half_words w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  square_input_bounds (half_words w) /\
  radix_value (half_words w) mod feP=@toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem a) /\
  lframe (fun bx _ => bx<>b) m mf.
Proof.
  intros HB HF HO HI.
  destruct (eval_field_half_numeric w m b HB HF HO) as (mf & HC & FF & FO & BO & VO & HL).
  exists mf;split;[exact HC|];split;[exact FF|];split;[exact FO|];split;[exact BO|].
  split;[exact (half_words_matches_literal w a HB HI)|exact HL].
Qed.

Theorem double_l_words_matches_literal w (a : Ty.tySem (Word 8)) :
  mul_small_input_bounds w -> radix_value w mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value (double_l_words w) mod feP=@toZ (WordToZ 8)
    (@literal_fe_halve Alg.CoreFunSem (@literal_fe_multiply_int 3 Alg.CoreFunSem a)).
Proof.
  intros HB HI;unfold double_l_words.
  apply half_words_matches_literal.
  - apply mul_small_output_bounds;[change (0<=3<=7);lia|exact HB].
  - rewrite (mul_small_radix (Int.repr 3) w ltac:(change (0<=3<=7);lia) HB).
    change ((3*radix_value w) mod feP=@toZ (WordToZ 8) (@literal_fe_multiply_int 3 Alg.CoreFunSem a) mod feP).
    rewrite literal_fe_multiply_int_numeric,Z.mod_mod by (unfold feP,feR;lia).
    rewrite <-(Z.mul_mod_idemp_r 3 (radix_value w) feP) by (unfold feP,feR;lia).
    rewrite HI;apply Z.mul_mod_idemp_r;unfold feP,feR;lia.
Qed.
