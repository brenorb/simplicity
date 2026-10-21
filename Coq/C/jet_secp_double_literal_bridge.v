(** Actual reader/double_var word outputs, decoded by the original field writer,
    against the complete literal Simplicity gej_double, including infinity. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_square_spec_bridge C.jet_secp_square_columns C.jet_secp_double_all_calls
  C.jet_secp_double_literal C.jet_secp_double_coordinate_numeric C.jet_secp_double_var_owned
  C.jet_secp_canonical_zero C.jet_secp_literal_gej_predicate C.jet_secp_literal_infinity
  C.jet_secp_rescale_literal.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_double_body literal_gej_double rescale_field_output.

Lemma double_field_output_matches w (a : Ty.tySem (Word 8)) :
  radix_value w mod feP=@toZ (WordToZ 8) a -> rescale_field_output w=a.
Proof.
  intro HE;apply (toZ_injective (WordToZ 8)).
  rewrite rescale_field_output_value,field_prime_matches_normalizer;exact HE.
Qed.
Theorem double_body_writer_outputs_literal x y z (a b c : Ty.tySem (Word 8)) :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  radix_value x mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value y mod feP=@toZ (WordToZ 8) b mod feP ->
  radix_value z mod feP=@toZ (WordToZ 8) c mod feP ->
  ((rescale_field_output (double_output_x_words x y),rescale_field_output (double_output_y_words x y)),
    rescale_field_output (double_output_z_words y z))=@literal_gej_double_body Alg.CoreFunSem ((a,b),c).
Proof.
  intros BX BY BZ HX HY HZ.
  destruct (double_body_coordinates_match x y z a b c BX BY BZ HX HY HZ) as (EX & EY & EZ).
  destruct (@literal_gej_double_body Alg.CoreFunSem ((a,b),c)) as [[ox oy] oz];cbn [fst snd] in EX,EY,EZ.
  f_equal.
  { f_equal.
    - apply double_field_output_matches;exact EX.
    - apply double_field_output_matches;exact EY. }
  { apply double_field_output_matches;exact EZ. }
Qed.

Theorem double_reader_outputs_literal (a b c : Ty.tySem (Word 8)) :
  let flag := bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem c)) in
  ((rescale_field_output (double_var_x_words flag (square_reader_rho a) (square_reader_rho b)),
    rescale_field_output (double_var_y_words flag (square_reader_rho a) (square_reader_rho b))),
    rescale_field_output (double_var_z_words flag (square_reader_rho b) (square_reader_rho c)))=
    @literal_gej_double Alg.CoreFunSem ((a,b),c).
Proof.
  cbn zeta;rewrite literal_gej_double_step,literal_gej_is_infinity_value.
  unfold bit_int,double_var_x_words,double_var_y_words,double_var_z_words.
  destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem c)) eqn:HE.
  - change (((rescale_field_output (fun _ : nat => Int64.zero),rescale_field_output (fun _ : nat => Int64.zero)),
      rescale_field_output (fun _ : nat => Int64.zero))=@literal_gej_infinity Alg.CoreFunSem tt).
    change (((rescale_field_output (fun _ : nat => Int64.zero),rescale_field_output (fun _ : nat => Int64.zero)),
      rescale_field_output (fun _ : nat => Int64.zero))=
      ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),@literal_fe_zero256 Alg.CoreFunSem tt)).
    assert (HZ : rescale_field_output (fun _ : nat => Int64.zero)=@literal_fe_zero256 Alg.CoreFunSem tt)
      by (exact zero_field_writer_literal_output).
    rewrite HZ;reflexivity.
  - change (((rescale_field_output (double_output_x_words (square_reader_rho a) (square_reader_rho b)),
      rescale_field_output (double_output_y_words (square_reader_rho a) (square_reader_rho b))),
      rescale_field_output (double_output_z_words (square_reader_rho b) (square_reader_rho c)))=
      @literal_gej_double_body Alg.CoreFunSem ((a,b),c)).
    apply double_body_writer_outputs_literal;
      try apply square_reader_bounds;
      rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.

Theorem eval_double_var_literal (a b c : Ty.tySem (Word 8)) m ba :
  Mem.load Mint32 m ba 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem c)))) ->
  fe_at m ba 0 (words5 (square_reader_rho a)) ->
  fe_at m ba 40 (words5 (square_reader_rho b)) ->
  fe_at m ba 80 (words5 (square_reader_rho c)) -> Mem.range_perm m ba 0 128 Cur Freeable ->
  exists mf x y z,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double_var)
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\
  square_input_bounds x /\ square_input_bounds y /\ square_input_bounds z /\
  ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=
    @literal_gej_double Alg.CoreFunSem ((a,b),c) /\ lframe (fun b _ => b<>ba) m mf.
Proof.
  intros HFlag HX HY HZ HF.
  destruct (eval_double_var_owned (square_reader_rho a) (square_reader_rho b) (square_reader_rho c) m ba
    (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem c)))
    (square_reader_bounds a) (square_reader_bounds b) (square_reader_bounds c) HFlag HX HY HZ HF)
    as (mf & HC & XF & YF & ZF & LF & FF & BX & BY & BZ & HL).
  exists mf;eexists;eexists;eexists.
  split;[exact HC|];split;[exact XF|];split;[exact YF|];split;[exact ZF|].
  split;[exact FF|];split;[exact BX|];split;[exact BY|];split;[exact BZ|].
  split;[apply double_reader_outputs_literal|exact HL].
Qed.
