(** The four actual wNAF arrays determine the literal full Strauss fold. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_secp_strauss_complete_program C.jet_secp_strauss_program
 C.jet_secp_strauss_general_loop C.jet_secp_strauss_general_loop_literal
 C.jet_secp_strauss_digit_index C.jet_secp_generator_digit_index
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_signed_array C.jet_secp_wnaf_literal
 C.jet_secp_wnaf_loop C.jet_secp_wnaf_literal_array C.jet_secp_wnaf_literal_values
 C.jet_secp_scalar_split128_literal C.jet_secp_split_literal
 C.jet_secp_scalar_table_literal C.jet_secp_literal_infinity C.jet_secp_negate_literal_contract.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_strauss_digits129 literal_wnaf5 literal_wnaf15 literal_gej_infinity
 literal_strauss_body literal_scalar_table5 literal_scalar_split_lambda literal_strauss_split128 literal_fe_multiply.
Local Opaque literal_scalar_split128 C.jet_secp_canonical_scalar.canonical_scalar_normalize.

Theorem strauss_four_arrays_loop_literal m b bg1 bg128
 (state1 statelam:Ty.tySem literal_wnaf_state) (wordg1 wordg128:Ty.tySem (Word 7))
 sign1 signlam last1 lastlam lastg1 lastg128 digits1 digitslam digitsg1 digitsg128
 (context:Ty.tySem literal_strauss_context) :
 wnaf_array_state m b 0 129 5 sign1 129 last1 digits1 ->
 wnaf_array_state m b 516 129 5 signlam 129 lastlam digitslam ->
 wnaf_array_state m bg1 0 129 15 1 129 lastg1 digitsg1 ->
 wnaf_array_state m bg128 0 129 15 1 129 lastg128 digitsg128 ->
 map wnaf5_literal_value (literal_wnaf5_digits state1)=
  rev (map (fun j=>sign1*digits1 (Z.of_nat j)) (seq 0 129)) ->
 map wnaf5_literal_value (literal_wnaf5_digits statelam)=
  rev (map (fun j=>signlam*digitslam (Z.of_nat j)) (seq 0 129)) ->
 map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,wordg1))=
  rev (map (fun j=>digitsg1 (Z.of_nat j)) (seq 0 129)) ->
 map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,wordg128))=
  rev (map (fun j=>digitsg128 (Z.of_nat j)) (seq 0 129)) ->
 strauss_general_loop_result
  (Z.to_nat (Z.max (Z.max (Z.max (last1+1) (lastlam+1)) (lastg1+1)) (lastg128+1)))
  (strauss_wnaf5_digit_at state1) (strauss_wnaf5_digit_at statelam)
  (wnaf_literal_digit_at wordg1) (wnaf_literal_digit_at wordg128) context
  (@literal_gej_infinity Alg.CoreFunSem tt)=
 @literal_strauss_digits129 Alg.CoreFunSem
  (@literal_gej_infinity Alg.CoreFunSem tt,(context,
   ((@literal_wnaf5 Alg.CoreFunSem state1,@literal_wnaf5 Alg.CoreFunSem statelam),
    (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,wordg1),@literal_wnaf15 Alg.CoreFunSem (Bit.zero,wordg128))))).
Proof.
 intros A1 AL AG1 AG128 L1 LL LG1 LG128.
 destruct (strauss_wnaf5_array_for_loop m b 0 state1 digits1 sign1 last1 A1 L1) as [B1 D1].
 destruct (strauss_wnaf5_array_for_loop m b 516 statelam digitslam signlam lastlam AL LL) as [BL DL].
 destruct (wnaf_literal_array_for_generator m bg1 0 wordg1 digitsg1 lastg1 AG1 LG1) as [BG1 DG1].
 destruct (wnaf_literal_array_for_generator m bg128 0 wordg128 digitsg128 lastg128 AG128 LG128) as [BG128 DG128].
 pose proof (strauss_wnaf5_digit_at_vectors state1 statelam) as PointDigits.
 pose proof (wnaf_literal_digit_at_vectors wordg1 wordg128) as GeneratorDigits.
 assert (Digits:map (fun j=>
  ((strauss_wnaf5_digit_at state1 (Z.of_nat j),strauss_wnaf5_digit_at statelam (Z.of_nat j)),
   (wnaf_literal_digit_at wordg1 (Z.of_nat j),wnaf_literal_digit_at wordg128 (Z.of_nat j)))) (rev (seq 0 129))=
  combine
   (map (fun j=>(strauss_wnaf5_digit_at state1 (Z.of_nat j),strauss_wnaf5_digit_at statelam (Z.of_nat j))) (rev (seq 0 129)))
   (map (fun j=>(wnaf_literal_digit_at wordg1 (Z.of_nat j),wnaf_literal_digit_at wordg128 (Z.of_nat j))) (rev (seq 0 129)))).
 { symmetry;apply generator_combine_map. }
 rewrite PointDigits,GeneratorDigits in Digits.
 destruct (@literal_wnaf5 Alg.CoreFunSem state1) as [h1 t1],
  (@literal_wnaf5 Alg.CoreFunSem statelam) as [hlam tlam],
  (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,wordg1)) as [hg1 tg1],
  (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,wordg128)) as [hg128 tg128].
 apply strauss_general_short_loop_literal129;[lia| |exact Digits].
 intros j [Lower Upper];assert (Range:0<=Z.of_nat j<129) by lia.
 assert (Above:Z.max (Z.max (Z.max (last1+1) (lastlam+1)) (lastg1+1)) (lastg128+1)<=Z.of_nat j).
 { apply Nat2Z.inj_le in Lower;rewrite Z2Nat.id in Lower by lia;exact Lower. }
 split;[apply (proj2 (D1 _ Range));lia|].
 split;[apply (proj2 (DL _ Range));lia|].
 split;[apply (proj2 (proj2 (DG1 _ Range)));lia|apply (proj2 (proj2 (DG128 _ Range)));lia].
Qed.

Lemma strauss_split128_halves raw :
 @literal_strauss_split128 Alg.CoreFunSem raw=
 (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,literal_split128_low raw),
  @literal_wnaf15 Alg.CoreFunSem (Bit.zero,literal_split128_high raw)).
Proof.
 assert (Pack:@literal_scalar_split128 Alg.CoreFunSem raw=
  ((inl tt,literal_split128_low raw),(inl tt,literal_split128_high raw))).
 { unfold literal_split128_low,literal_split128_high.
   pose proof (literal_scalar_split128_step raw) as SplitValue.
   destruct (@literal_scalar_split128 Alg.CoreFunSem raw) as [[tag0 x][tag1 y]] eqn:Split.
   pose proof (f_equal (fun p=>fst (fst p)) SplitValue) as Tag0.
   pose proof (f_equal (fun p=>fst (snd p)) SplitValue) as Tag1.
   change (tag0=inl tt) in Tag0;change (tag1=inl tt) in Tag1.
   rewrite Tag0,Tag1;reflexivity. }
 rewrite literal_strauss_split128_value.
 exact (f_equal (fun split=>
  (@literal_wnaf15 Alg.CoreFunSem (fst split),@literal_wnaf15 Alg.CoreFunSem (snd split))) Pack).
Qed.

Theorem strauss_body_from_four_arrays m b bg1 bg128
 (raw ng:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej)
 sign1 signlam last1 lastlam lastg1 lastg128 digits1 digitslam digitsg1 digitsg128 :
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 wnaf_array_state m b 0 129 5 sign1 129 last1 digits1 ->
 wnaf_array_state m b 516 129 5 signlam 129 lastlam digitslam ->
 wnaf_array_state m bg1 0 129 15 1 129 lastg1 digitsg1 ->
 wnaf_array_state m bg128 0 129 15 1 129 lastg128 digitsg128 ->
 map wnaf5_literal_value (literal_wnaf5_digits (fst halves))=
  rev (map (fun j=>sign1*digits1 (Z.of_nat j)) (seq 0 129)) ->
 map wnaf5_literal_value (literal_wnaf5_digits (snd halves))=
  rev (map (fun j=>signlam*digitslam (Z.of_nat j)) (seq 0 129)) ->
 map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,literal_split128_low ng))=
  rev (map (fun j=>digitsg1 (Z.of_nat j)) (seq 0 129)) ->
 map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,literal_split128_high ng))=
  rev (map (fun j=>digitsg128 (Z.of_nat j)) (seq 0 129)) ->
 let context:=@literal_scalar_table5 Alg.CoreFunSem point in
 let result:=strauss_general_loop_result
  (Z.to_nat (Z.max (Z.max (Z.max (last1+1) (lastlam+1)) (lastg1+1)) (lastg128+1)))
  (strauss_wnaf5_digit_at (fst halves)) (strauss_wnaf5_digit_at (snd halves))
  (wnaf_literal_digit_at (literal_split128_low ng)) (wnaf_literal_digit_at (literal_split128_high ng)) context
  (@literal_gej_infinity Alg.CoreFunSem tt) in
 (fst result,@literal_fe_multiply Alg.CoreFunSem (fst context,snd result))=
 @literal_strauss_body Alg.CoreFunSem ((raw,point),ng).
Proof.
 cbv zeta;intros A1 AL AG1 AG128 L1 LL LG1 LG128.
 pose proof (strauss_four_arrays_loop_literal m b bg1 bg128
  (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw))
  (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw))
  (literal_split128_low ng) (literal_split128_high ng)
  sign1 signlam last1 lastlam lastg1 lastg128 digits1 digitslam digitsg1 digitsg128
  (@literal_scalar_table5 Alg.CoreFunSem point) A1 AL AG1 AG128 L1 LL LG1 LG128) as Fold.
 symmetry;rewrite literal_strauss_body_value,literal_strauss_split_lambda_value,strauss_split128_halves.
 exact (eq_sym (f_equal (fun result:Ty.tySem literal_table_gej=>
  (fst result,@literal_fe_multiply Alg.CoreFunSem
   (fst (@literal_scalar_table5 Alg.CoreFunSem point),snd result))) Fold)).
Qed.
