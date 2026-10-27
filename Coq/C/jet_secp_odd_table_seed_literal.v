(** Establish the literal first-pass relations for the original C head/seed
    outputs. The finite-input condition is the caller's existing Z/flag
    invariant; neither a curve equation nor a nonzero doubled Z is required. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_rescale_literal
 C.jet_secp_scalar_table_literal C.jet_secp_odd_table_literal_walk
 C.jet_secp_odd_table_body C.jet_secp_odd_table_seed C.jet_secp_odd_table_loop
 C.jet_secp_double_all_calls C.jet_secp_double_coordinate_numeric
 C.jet_secp_double_literal_bridge C.jet_secp_double_literal C.jet_secp_literal_gej_predicate
 C.jet_secp_ge_zinv_literal C.jet_secp_ge_zinv_arithmetic C.jet_secp_ge_zinv_factor
 C.jet_secp_point_mul_numeric C.jet_secp_field_zero_owned C.jet_secp_mixed_xy_flag
 C.jet_secp_canonical_zero C.jet_readBit_layout C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_negate_literal_contract.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_gej_double literal_gej_double_body literal_gej_zinv
 literal_pass1_8 literal_pass2_8 rescale_field_output.

Lemma literal_scalar_table5_route (p:Ty.tySem literal_table_gej) :
 let d:Ty.tySem literal_table_gej:=@literal_gej_double Alg.CoreFunSem p in
 let start:Ty.tySem literal_table_gej:=(@literal_gej_zinv Alg.CoreFunSem (fst p,snd d),snd p) in
 let first:Ty.tySem (Ty.Prod (literal_table_tree 3) (Word 8)):=
  @literal_pass1_8 Alg.CoreFunSem (start,fst d) in
 @literal_scalar_table5 Alg.CoreFunSem p=
 (@literal_fe_multiply Alg.CoreFunSem (snd d,snd first),
  @literal_pass2_8 Alg.CoreFunSem (fst first)).
Proof. destruct p as [[x y] z];reflexivity. Qed.

Lemma table_finite_double_literal x y z (a b c:Ty.tySem (Word 8)) :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 table_word_literal x a -> table_word_literal y b -> table_word_literal z c ->
 field_zero_result z=Int.zero ->
 ((rescale_field_output (double_output_x_words x y),
   rescale_field_output (double_output_y_words x y)),
   rescale_field_output (double_output_z_words y z))=
 @literal_gej_double Alg.CoreFunSem ((a,b),c).
Proof.
 intros BX BY BZ HX HY HZ Finite.
 pose proof (mixed_flag_of_residue z c HZ) as Flag.
 assert (Nonzero:Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem c)=Datatypes.false).
 { rewrite Finite in Flag;unfold bit_int in Flag.
   destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem c));[discriminate Flag|reflexivity]. }
 rewrite literal_gej_double_step,literal_gej_is_infinity_value,Nonzero.
 apply double_body_writer_outputs_literal;assumption.
Qed.

Theorem odd_table_initial_literal x y z (a b c:Ty.tySem (Word 8)) :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 table_word_literal x a -> table_word_literal y b -> table_word_literal z c ->
 field_zero_result z=Int.zero ->
 let d:Ty.tySem literal_table_gej:=@literal_gej_double Alg.CoreFunSem ((a,b),c) in
 let start:Ty.tySem literal_table_gej:=(@literal_gej_zinv Alg.CoreFunSem ((a,b),snd d),c) in
 table_acc_literal (odd_table_initial_state x y z) start /\
 table_prefix_literal 1 (odd_table_initial_state x y z) start (fst d) /\
 table_word_literal (double_output_x_words x y) (fst (fst d)) /\
 table_word_literal (double_output_y_words x y) (snd (fst d)).
Proof.
 intros BX BY BZ HX HY HZ Finite;cbv zeta.
 pose proof (table_finite_double_literal x y z a b c BX BY BZ HX HY HZ Finite) as Double.
 assert (DZ:table_word_literal (double_output_z_words y z)
  (snd (@literal_gej_double Alg.CoreFunSem ((a,b),c)))).
 { apply table_decoded_literal;exact (f_equal snd Double). }
 assert (BoundDZ:square_input_bounds (double_output_z_words y z)).
 { unfold double_output_z_words;apply double_tight_loose,double_mul_tight;assumption. }
 pose proof (ge_zinv_words_literal x y (double_output_z_words y z) a b
  (snd (@literal_gej_double Alg.CoreFunSem ((a,b),c))) BX BY BoundDZ HX HY DZ) as Scaled.
 assert (SX:table_word_literal (ge_zinv_x_words x (double_output_z_words y z))
  (fst (@literal_gej_zinv Alg.CoreFunSem ((a,b),snd (@literal_gej_double Alg.CoreFunSem ((a,b),c)))))).
 { apply table_decoded_literal;exact (f_equal fst Scaled). }
 assert (SY:table_word_literal (ge_zinv_y_words y (double_output_z_words y z))
  (snd (@literal_gej_zinv Alg.CoreFunSem ((a,b),snd (@literal_gej_double Alg.CoreFunSem ((a,b),c)))))).
 { apply table_decoded_literal;exact (f_equal snd Scaled). }
 split.
 - unfold table_acc_literal,odd_table_initial_state,odd_table_seed_state;
   cbn [odd_table_x odd_table_y odd_table_z odd_table_flag fst snd];
   split;[exact SX|];split;[exact SY|];split;[exact HZ|symmetry;exact Finite].
 - split.
   + intros j Range;assert (j=0)%nat by lia;subst j.
     split;[exact SX|];split;[exact SY|];intros;lia.
   + split.
     * apply table_decoded_literal;exact (f_equal (fun p=>fst (fst p)) Double).
     * apply table_decoded_literal;exact (f_equal (fun p=>snd (fst p)) Double).
Qed.
