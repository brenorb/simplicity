(** Exact value of the actual typed second-stage outputs.
    Stage guards below are internal obligations, derived from the first fold
    at composition, not new public jet assumptions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values.
Require Import C.jet_sx_expr.
Require Import C.jet_secp_reduce512_wide C.jet_secp_reduce512_symbolic
  C.jet_secp_reduce512_accumulate C.jet_secp_reduce512_typed_stage
  C.jet_secp_reduce512_typed_atomic C.jet_secp_reduce512_first_value
  C.jet_secp_reduce512_fold_bounds C.jet_secp_scalar_mul512_accumulate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Section TYPED.
Variable digits : nat -> int64.
Variable m6 : int.
Definition stage_ops1 := [Wmul (digits 5%nat) wide_C0; Wmul (digits 4%nat) wide_C1].
Definition stage_ops2 := [Wsum (digits 2%nat); Wmul (stage_ma_m6 m6) wide_C0;
  Wmul (digits 5%nat) wide_C1; Wsum (digits 4%nat)].
Definition stage_low256 := column_words_value [digits 0%nat; digits 1%nat; digits 2%nat; digits 3%nat].
Definition stage_high256 := column_words_value [digits 4%nat; digits 5%nat; stage_ma_m6 m6].
Definition stage_prefix := [wlo (stage_ma0 digits); wlo (stage_ma1 digits);
  wlo (stage_ma2 digits m6); wlo (stage_ma3 digits m6)].
Definition stage_p4_integer := Int64.unsigned (whi (stage_ma3 digits m6)) + Int64.unsigned (stage_ma_m6 m6).
Lemma stage_m6_unsigned : Int64.unsigned (stage_ma_m6 m6) = Int.unsigned m6.
Proof.
  unfold stage_ma_m6; apply Int64.unsigned_repr.
  pose proof (Int.unsigned_range m6); change Int.modulus with 4294967296 in *.
  change Int64.max_unsigned with 18446744073709551615; lia.
Qed.
Lemma stage_carry0_bound : wide_value (wide_extract_fast (stage_ma0 digits)) < Int64.modulus.
Proof.
  unfold wide_value; cbn [wide_extract_fast wlo whi wtop].
  change (Int64.unsigned (whi (stage_ma0 digits)) + Int64.modulus *
    (Int64.unsigned Int64.zero + Int64.modulus * Int64.unsigned Int64.zero) < Int64.modulus).
  rewrite Int64.unsigned_zero; pose proof (Int64.unsigned_range (whi (stage_ma0 digits))); nia.
Qed.
Lemma stage_column_values : Int.unsigned m6 <= 1 ->
  wide_value (stage_ma0 digits) = Int64.unsigned (digits 0%nat) + Int64.unsigned (digits 4%nat) * Int64.unsigned wide_C0 /\
  wide_value (stage_ma1 digits) = wide_value (wide_extract_fast (stage_ma0 digits)) + Int64.unsigned (digits 1%nat) + wide_operation_sum stage_ops1 /\
  wide_value (stage_ma2 digits m6) = wide_value (wide_extract (stage_ma1 digits)) + wide_operation_sum stage_ops2 /\
  wide_value (stage_ma3 digits m6) = wide_value (wide_extract (stage_ma2 digits m6)) + Int64.unsigned (digits 3%nat) +
    Int64.unsigned (stage_ma_m6 m6) * Int64.unsigned wide_C1 + Int64.unsigned (digits 5%nat).
Proof.
  intro Hm6; pose proof (Int.unsigned_range m6).
  pose proof Int64.modulus_pos.
  assert (HM : 8 < Int64.modulus) by (change (8 < 18446744073709551616); lia).
  assert (E0 : wide_value (stage_ma0 digits) = Int64.unsigned (digits 0%nat) + Int64.unsigned (digits 4%nat) * Int64.unsigned wide_C0).
  { unfold stage_ma0; rewrite wide_muladd_fast_value; [rewrite wide_from_word_value; reflexivity|reflexivity|].
    rewrite wide_from_word_value; pose proof (Int64.unsigned_range (digits 0%nat));
    pose proof (Int64.unsigned_range (digits 4%nat)); pose proof (Int64.unsigned_range wide_C0); nia. }
  pose proof stage_carry0_bound as HC0.
  pose proof (Int64.unsigned_range (digits 1%nat)) as HX1.
  assert (ES1 : wide_value (wide_sumadd_fast (digits 1%nat) (wide_extract_fast (stage_ma0 digits))) =
    wide_value (wide_extract_fast (stage_ma0 digits)) + Int64.unsigned (digits 1%nat)).
  { apply wide_sumadd_fast_value; [reflexivity|nia]. }
  assert (HS1 : wide_value (wide_sumadd_fast (digits 1%nat) (wide_extract_fast (stage_ma0 digits))) < 5 * Int64.modulus)
    by (rewrite ES1; nia).
  destruct (wide_accumulate_small stage_ops1 _ ltac:(cbn [stage_ops1 length]; lia) HS1) as [E1 [_ H1]].
  change (wide_value (wide_extract (stage_ma1 digits)) < 5 * Int64.modulus) in H1.
  change (wide_value (stage_ma1 digits) = wide_value (wide_sumadd_fast (digits 1%nat) (wide_extract_fast (stage_ma0 digits))) + wide_operation_sum stage_ops1) in E1.
  rewrite ES1 in E1.
  destruct (wide_accumulate_small stage_ops2 _ ltac:(cbn [stage_ops2 length]; lia) H1) as [E2 [_ H2]].
  change (wide_value (wide_extract (stage_ma2 digits m6)) < 5 * Int64.modulus) in H2.
  change (wide_value (stage_ma2 digits m6) = wide_value (wide_extract (stage_ma1 digits)) + wide_operation_sum stage_ops2) in E2.
  pose proof (Int64.unsigned_range (digits 3%nat)) as HX3.
  pose proof (Int64.unsigned_range (digits 5%nat)) as HX5.
  pose proof (Int64.unsigned_range wide_C1) as HC1.
  assert (HP : Int64.unsigned (stage_ma_m6 m6) * Int64.unsigned wide_C1 < Int64.modulus)
    by (rewrite stage_m6_unsigned; nia).
  assert (ES3 : wide_value (wide_sumadd_fast (digits 3%nat) (wide_extract (stage_ma2 digits m6))) =
    wide_value (wide_extract (stage_ma2 digits m6)) + Int64.unsigned (digits 3%nat)).
  { apply wide_sumadd_fast_value; [reflexivity|nia]. }
  assert (EM3 : wide_value (wide_muladd_fast (stage_ma_m6 m6) wide_C1
      (wide_sumadd_fast (digits 3%nat) (wide_extract (stage_ma2 digits m6)))) =
    wide_value (wide_extract (stage_ma2 digits m6)) + Int64.unsigned (digits 3%nat) +
      Int64.unsigned (stage_ma_m6 m6) * Int64.unsigned wide_C1).
  { rewrite wide_muladd_fast_value; [rewrite ES3; reflexivity|reflexivity|rewrite ES3; nia]. }
  assert (E3 : wide_value (stage_ma3 digits m6) = wide_value (wide_extract (stage_ma2 digits m6)) +
    Int64.unsigned (digits 3%nat) + Int64.unsigned (stage_ma_m6 m6) * Int64.unsigned wide_C1 + Int64.unsigned (digits 5%nat)).
  { unfold stage_ma3; rewrite wide_sumadd_fast_value; [rewrite EM3; reflexivity|reflexivity|rewrite EM3; nia]. }
  exact (conj E0 (conj E1 (conj E2 E3))).
Qed.
Lemma stage_reconstruction : Int.unsigned m6 <= 1 ->
  column_words_value stage_prefix + reduce512_radix * stage_p4_integer = stage_low256 + stage_high256 * first_delta.
Proof.
  intro Hm6; destruct (stage_column_values Hm6) as [E0 [E1 [E2 E3]]].
  pose proof (wide_extract_fast_decomposition (stage_ma0 digits) eq_refl) as D0.
  pose proof (wide_extract_decomposition (stage_ma1 digits)) as D1.
  pose proof (wide_extract_decomposition (stage_ma2 digits m6)) as D2.
  pose proof (wide_extract_fast_decomposition (stage_ma3 digits m6) eq_refl) as D3.
  assert (DC : wide_value (wide_extract_fast (stage_ma3 digits m6)) = Int64.unsigned (whi (stage_ma3 digits m6))).
  { unfold wide_value; cbn [wide_extract_fast wlo whi wtop].
    change (Int64.unsigned (whi (stage_ma3 digits m6)) + Int64.modulus *
      (Int64.unsigned Int64.zero + Int64.modulus * Int64.unsigned Int64.zero) = Int64.unsigned (whi (stage_ma3 digits m6))).
    rewrite Int64.unsigned_zero; ring. }
  rewrite DC in D3.
  cbn [stage_ops1 stage_ops2 wide_operation_sum wide_operation_value] in E1,E2.
  unfold stage_prefix,stage_p4_integer,stage_low256,stage_high256,first_delta,reduce512_radix.
  cbn [column_words_value]; change Int64.modulus with 18446744073709551616 in *; cbn [Z.pow]; nia.
Qed.
Lemma stage_p4_bound : Int.unsigned m6 <= 1 -> stage_high256 <= first_delta -> 0 <= stage_p4_integer <= 2.
Proof.
  intros Hm6 HH; pose proof (stage_reconstruction Hm6) as HE.
  pose proof (column_words_bound [digits 0%nat; digits 1%nat; digits 2%nat; digits 3%nat]) as HL.
  change (0 <= stage_low256 < reduce512_radix) in HL.
  pose proof (column_words_bound [digits 4%nat; digits 5%nat; stage_ma_m6 m6]) as Hhigh.
  change (0 <= stage_high256 < Int64.modulus ^ 3) in Hhigh.
  pose proof (column_words_bound stage_prefix) as HP.
  destruct reduce512_delta_bounds as [HD [HD2 _]].
  assert (HT : 0 <= stage_low256 + stage_high256 * first_delta < 3 * reduce512_radix) by nia.
  assert (HR : 0 < reduce512_radix) by (unfold reduce512_radix; change (0 < 115792089237316195423570985008687907853269984665640564039457584007913129639936); lia).
  assert (HC : 0 <= stage_p4_integer) by (unfold stage_p4_integer; pose proof (Int64.unsigned_range (whi (stage_ma3 digits m6))); pose proof (Int64.unsigned_range (stage_ma_m6 m6)); lia).
  nia.
Qed.
Lemma stage_p4_unsigned : Int.unsigned m6 <= 1 -> stage_high256 <= first_delta ->
  Int64.unsigned (Int64.repr (Int.unsigned (Int64.loword (Int64.add (whi (stage_ma3 digits m6)) (stage_ma_m6 m6))))) = stage_p4_integer.
Proof.
  intros Hm6 HH; pose proof (stage_p4_bound Hm6 HH) as HB.
  assert (HA : Int64.unsigned (Int64.add (whi (stage_ma3 digits m6)) (stage_ma_m6 m6)) = stage_p4_integer).
  { rewrite Int64.add_unsigned,Int64.unsigned_repr; [reflexivity|fold stage_p4_integer; change Int64.max_unsigned with 18446744073709551615; lia]. }
  unfold Int64.loword; rewrite HA,Int.unsigned_repr; [|change Int.max_unsigned with 4294967295; lia].
  rewrite Int64.unsigned_repr; [reflexivity|change Int64.max_unsigned with 18446744073709551615; lia].
Qed.
Theorem stage_machine_value : Int.unsigned m6 <= 1 -> stage_high256 <= first_delta ->
  column_words_value (stage_machine_outputs digits m6) = stage_low256 + stage_high256 * first_delta.
Proof.
  intros Hm6 HH.
  change (column_words_value (stage_prefix ++ [Int64.repr (Int.unsigned (Int64.loword
    (Int64.add (whi (stage_ma3 digits m6)) (stage_ma_m6 m6))))]) = stage_low256 + stage_high256 * first_delta).
  rewrite column_words_append.
  change (column_words_value stage_prefix + reduce512_radix *
    (Int64.unsigned (Int64.repr (Int.unsigned (Int64.loword (Int64.add (whi (stage_ma3 digits m6)) (stage_ma_m6 m6))))) + Int64.modulus * 0) =
    stage_low256 + stage_high256 * first_delta).
  rewrite (stage_p4_unsigned Hm6 HH),Z.mul_0_r,Z.add_0_r; apply stage_reconstruction; exact Hm6.
Qed.
Theorem typed_second_source_value rho beta : Int.unsigned m6 <= 1 -> stage_high256 <= first_delta ->
  column_words_value (map (fun sy => il (den rho beta sy)) (reduce512_typed_stage_limbs digits m6)) =
    stage_low256 + stage_high256 * first_delta.
Proof.
  intros Hm6 HH.
  change (column_words_value (map il (map (den rho beta) (reduce512_typed_stage_limbs digits m6))) = stage_low256 + stage_high256 * first_delta).
  rewrite stage_outputs_machine,map_map.
  change (column_words_value (stage_machine_outputs digits m6) = stage_low256 + stage_high256 * first_delta).
  apply stage_machine_value; assumption.
Qed.
End TYPED.
