(** The frozen split_lambda Core terms have the exact small signed values
    established for the original C scalar_split_lambda helper. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_toZ C.jet_predicate_spec C.jet_multiply_spec C.jet_subtract_spec
 C.jet_secp_canonical_scalar C.jet_secp_canonical_scalar_add
 C.jet_secp_canonical_scalar_add_numeric C.jet_secp_canonical_scalar_negate
 C.jet_secp_canonical_scalar_lambda C.jet_secp_scalar_mul_literal_numeric
 C.jet_secp_split_multipliers C.jet_secp_scalar_lambda_global
 C.jet_secp_split_round_literal C.jet_secp_split_constants C.jet_secp_split_signed_bounds
 C.jet_secp_split_literal C.jet_secp_split_half_numeric C.jet_secp_split_pack_numeric C.jet_secp_wnaf5_input.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque multiply_word_spec subtract_word_spec literal_split_coefficient
 Alg.scribe canonical_scalar_add canonical_scalar_multiply canonical_scalar_negate.

Lemma literal_split_basis_range first : 0<=literal_split_basis_value first<2^128.
Proof.
 destruct first;cbv [literal_split_basis_value split_basis_value split_lattice_b2];lia.
Qed.
Lemma literal_split_basis_word_value first :
 @toZ (WordToZ 7) (literal_split_basis_word first)=literal_split_basis_value first.
Proof.
 unfold literal_split_basis_word;rewrite to_fromZ;apply Z.mod_small.
 change (0<=literal_split_basis_value first<2^128);apply literal_split_basis_range.
Qed.
Lemma literal_split_product_numeric first k :
 @toZ (WordToZ 8) (@literal_split_product first Alg.CoreFunSem k)=
 split_coefficient first (@toZ (WordToZ 8) k)*literal_split_basis_value first.
Proof.
 change (@toZ (WordToZ 8) (@multiply_word_spec 7 Alg.CoreFunSem
  (@literal_split_coefficient first Alg.CoreFunSem k,
   @Alg.scribe Ty.Unit (Word 7) (literal_split_basis_word first) Alg.CoreFunSem tt))=
  split_coefficient first (@toZ (WordToZ 8) k)*literal_split_basis_value first).
 rewrite Alg.scribe_correct,multiply_word_spec_numeric,literal_split_coefficient_numeric,
  literal_split_basis_word_value;reflexivity.
Qed.
Lemma literal_split_second_step k :
 @literal_split_second Alg.CoreFunSem k=
 let p:=@subtract_word_spec Alg.CoreFunSem 8
  (@literal_split_product Datatypes.true Alg.CoreFunSem k,
   @literal_split_product Datatypes.false Alg.CoreFunSem k) in (fst p,snd (snd p)).
Proof. reflexivity. Qed.
Local Opaque literal_split_product literal_split_second.
Theorem literal_split_second_numeric k :
 0<= @toZ (WordToZ 8) k<canonical_group_order ->
 split_half_signed (@literal_split_second Alg.CoreFunSem k)=split_signed_second (@toZ (WordToZ 8) k).
Proof.
 intro K.
 assert (Difference:
  @toZ (WordToZ 8) (@literal_split_product Datatypes.true Alg.CoreFunSem k)-
  @toZ (WordToZ 8) (@literal_split_product Datatypes.false Alg.CoreFunSem k)=
  split_signed_second (@toZ (WordToZ 8) k)).
 { rewrite !literal_split_product_numeric.
   unfold split_signed_second,literal_split_basis_value;ring. }
 pose proof (proj2 (split_signed_bounds _ K)) as Small.
 pose proof (split_subtract_half_numeric
  (@literal_split_product Datatypes.true Alg.CoreFunSem k)
  (@literal_split_product Datatypes.false Alg.CoreFunSem k)
  ltac:(rewrite Difference;exact Small)) as Half.
 rewrite literal_split_second_step;exact (eq_trans Half Difference).
Qed.
Corollary literal_split_second_residue k :
 0<= @toZ (WordToZ 8) k<canonical_group_order ->
 wnaf5_input_scalar (fst (@literal_split_second Alg.CoreFunSem k))
  (snd (@literal_split_second Alg.CoreFunSem k))=split_second_value (@toZ (WordToZ 8) k).
Proof. intro K;rewrite split_half_residue,literal_split_second_numeric by exact K;symmetry;apply split_second_signed. Qed.

Definition literal_split_first_scalar (k:Ty.tySem (Word 8)) (second:Ty.tySem literal_split_half) :=
 @canonical_scalar_add Alg.CoreFunSem (k,@canonical_scalar_negate Alg.CoreFunSem
  (@canonical_scalar_multiply Alg.CoreFunSem
   (@literal_split_signed_scalar Alg.CoreFunSem second,canonical_lambda_word))).
Lemma literal_split_first_step k second :
 @literal_split_first Alg.CoreFunSem (k,second)=
 @literal_split_pack_half Alg.CoreFunSem (literal_split_first_scalar k second).
Proof.
 unfold literal_split_first,literal_split_first_scalar.
 change (@literal_split_pack_half Alg.CoreFunSem
  (@canonical_scalar_add Alg.CoreFunSem (k,@canonical_scalar_negate Alg.CoreFunSem
   (@canonical_scalar_multiply Alg.CoreFunSem
    (@literal_split_signed_scalar Alg.CoreFunSem second,
     @Alg.scribe Ty.Unit (Word 8) canonical_lambda_word Alg.CoreFunSem tt))))=
 @literal_split_pack_half Alg.CoreFunSem
  (@canonical_scalar_add Alg.CoreFunSem (k,@canonical_scalar_negate Alg.CoreFunSem
   (@canonical_scalar_multiply Alg.CoreFunSem
    (@literal_split_signed_scalar Alg.CoreFunSem second,canonical_lambda_word))))).
 rewrite Alg.scribe_correct;reflexivity.
Qed.
Local Opaque literal_split_first literal_split_signed_scalar literal_split_pack_half.
Theorem literal_split_first_scalar_numeric k :
 0<= @toZ (WordToZ 8) k<canonical_group_order ->
 @toZ (WordToZ 8) (literal_split_first_scalar k (@literal_split_second Alg.CoreFunSem k))=
 split_first_value (@toZ (WordToZ 8) k).
Proof.
 intro K;unfold literal_split_first_scalar.
 rewrite canonical_scalar_add_numeric,canonical_scalar_negate_numeric,canonical_scalar_multiply_numeric,
  literal_split_signed_scalar_numeric,canonical_lambda_word_value,literal_split_second_residue by exact K.
 unfold split_first_value,split_negated_value,split_lambda_product;f_equal;ring.
Qed.
Theorem literal_split_first_numeric k :
 0<= @toZ (WordToZ 8) k<canonical_group_order ->
 split_half_signed (@literal_split_first Alg.CoreFunSem
  (k,@literal_split_second Alg.CoreFunSem k))=split_signed_first (@toZ (WordToZ 8) k).
Proof.
 intro K;rewrite literal_split_first_step;apply literal_split_pack_half_numeric.
 - exact (proj1 (split_signed_bounds _ K)).
 - rewrite literal_split_first_scalar_numeric by exact K;apply split_first_signed.
Qed.
Corollary literal_split_first_residue k :
 0<= @toZ (WordToZ 8) k<canonical_group_order ->
 wnaf5_input_scalar (fst (@literal_split_first Alg.CoreFunSem (k,@literal_split_second Alg.CoreFunSem k)))
  (snd (@literal_split_first Alg.CoreFunSem (k,@literal_split_second Alg.CoreFunSem k)))=
 split_first_value (@toZ (WordToZ 8) k).
Proof. intro K;rewrite split_half_residue,literal_split_first_numeric by exact K;symmetry;apply split_first_signed. Qed.

Local Opaque canonical_scalar_normalize literal_scalar_split_lambda.
Theorem literal_scalar_split_lambda_residues raw :
 let k:=@canonical_scalar_normalize Alg.CoreFunSem raw in
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 wnaf5_input_scalar (fst (fst halves)) (snd (fst halves))=split_first_value (@toZ (WordToZ 8) k) /\
 wnaf5_input_scalar (fst (snd halves)) (snd (snd halves))=split_second_value (@toZ (WordToZ 8) k).
Proof.
 cbv zeta.
 pose (k:=@canonical_scalar_normalize Alg.CoreFunSem raw).
 assert (K:0<= @toZ (WordToZ 8) k<canonical_group_order).
 { unfold k;rewrite canonical_scalar_normalize_numeric;apply Z.mod_pos_bound.
   pose proof canonical_group_order_range;lia. }
 rewrite literal_scalar_split_lambda_step;fold k;cbn [fst snd].
 split;[apply literal_split_first_residue|apply literal_split_second_residue];exact K.
Qed.

