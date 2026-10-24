(** Faithful complete generate tree, LibSecp256k1.hs:614--627,792.
    Existing literal ports supply scalar_split_128, wnaf15 and step129.
    This is a proof adapter; the frozen specification is not edited. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_secp_literal_infinity C.jet_secp_generate_literal
  C.jet_secp_generator_program C.jet_secp_wnaf_literal C.jet_secp_scalar_split128_literal.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_generate {term : Alg.Core.Algebra} :
  term (Word 8) literal_generator_jacobian :=
  ((unit >>> @literal_gej_infinity term) &&&
   (@literal_scalar_split128 term >>> (O (@literal_wnaf15 term) &&& I (@literal_wnaf15 term)))) >>>
  @literal_generator_digits129 term.

Local Opaque literal_generator_digits129 literal_gej_infinity literal_wnaf15.

Lemma literal_generate_value value :
  @literal_generate Alg.CoreFunSem value=
  @literal_generator_digits129 Alg.CoreFunSem (@literal_gej_infinity Alg.CoreFunSem tt,
    (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,literal_split128_low value),
     @literal_wnaf15 Alg.CoreFunSem (Bit.zero,literal_split128_high value))).
Proof.
  assert (Rebuild:forall (s:Ty.tySem (Ty.Prod (Ty.Prod Bit.Bit (Word 7)) (Ty.Prod Bit.Bit (Word 7))))
    (lo hi:Ty.tySem (Word 7)),s=((Bit.zero,lo),(Bit.zero,hi)) ->
    s=((Bit.zero,snd (fst s)),(Bit.zero,snd (snd s)))).
  { intros s lo hi ->;reflexivity. }
  assert (Split:@literal_scalar_split128 Alg.CoreFunSem value=
    ((Bit.zero,literal_split128_low value),(Bit.zero,literal_split128_high value))).
  { exact (Rebuild _ _ _ (literal_scalar_split128_step value)). }
  change (@literal_generator_digits129 Alg.CoreFunSem (@literal_gej_infinity Alg.CoreFunSem tt,
    (@literal_wnaf15 Alg.CoreFunSem (fst (@literal_scalar_split128 Alg.CoreFunSem value)),
     @literal_wnaf15 Alg.CoreFunSem (snd (@literal_scalar_split128 Alg.CoreFunSem value))))=
    @literal_generator_digits129 Alg.CoreFunSem (@literal_gej_infinity Alg.CoreFunSem tt,
      (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,literal_split128_low value),
       @literal_wnaf15 Alg.CoreFunSem (Bit.zero,literal_split128_high value)))).
  exact (f_equal (fun split=>@literal_generator_digits129 Alg.CoreFunSem
    (@literal_gej_infinity Alg.CoreFunSem tt,
      (@literal_wnaf15 Alg.CoreFunSem (fst split),@literal_wnaf15 Alg.CoreFunSem (snd split)))) Split).
Qed.

Lemma literal_generate_parametric : Alg.Core.Parametric (@literal_generate).
Proof.
  intros t1 t2 R;unfold literal_generate.
  repeat first [apply literal_generator_digits129_parametric|apply literal_scalar_split128_parametric|
    apply literal_gej_infinity_parametric|apply literal_wnaf15_parametric|
    apply Alg.comp_Parametric|apply Alg.pair_Parametric|apply Alg.take_Parametric|
    apply Alg.drop_Parametric|apply Alg.unit_Parametric].
Qed.
