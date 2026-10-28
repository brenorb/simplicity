(** Relate original signed preprocessing arrays to the literal scale body. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_secp_strauss_complete_program C.jet_secp_strauss_program
 C.jet_secp_scalar_split128_literal C.jet_secp_wnaf_literal C.jet_secp_wnaf5_literal
 C.jet_secp_literal_infinity C.jet_secp_scalar_table_literal C.jet_secp_split_literal
 C.jet_secp_negate_literal_contract C.jet_secp_generate_program.
Require Import C.jet_secp_literal_gej_predicate C.jet_secp_canonical_scalar_zero.
Local Opaque literal_strauss_body literal_strauss_guard literal_strauss_split128
 literal_scalar_table5 literal_scalar_split_lambda literal_scalar_split128
 literal_wnaf5 literal_wnaf15 literal_gej_infinity literal_strauss_digits129 literal_fe_multiply
 literal_gej_is_infinity canonical_scalar_is_zero literal_generate Word.zero.

From Coq Require Import ZArith List Lia.
Require Import C.jet_toZ C.jet_secp_canonical_scalar
 C.jet_secp_strauss_generator_zero C.jet_secp_strauss_scale_loop
 C.jet_secp_strauss_digit_index C.jet_secp_wnaf_loop C.jet_secp_wnaf5_signed_array.
Import ListNotations.
Local Open Scope Z_scope.
Local Opaque literal_strauss_digits129 literal_wnaf5 literal_wnaf15.

Lemma strauss_split128_zero_halves :
 literal_split128_low (@Word.zero 8 Alg.CoreFunSem tt)=@Word.zero 7 Alg.CoreFunSem tt /\
 literal_split128_high (@Word.zero 8 Alg.CoreFunSem tt)=@Word.zero 7 Alg.CoreFunSem tt.
Proof.
 assert (Normalized:@toZ (WordToZ 8)
  (@canonical_scalar_normalize Alg.CoreFunSem (@Word.zero 8 Alg.CoreFunSem tt))=0).
 { rewrite canonical_scalar_normalize_numeric,Word.zero_correct.
   apply Z.mod_0_l;pose proof canonical_group_order_range;lia. }
 destruct (literal_scalar_split128_numeric (@Word.zero 8 Alg.CoreFunSem tt)) as [Low High].
 rewrite Normalized in Low,High.
 change (@toZ (WordToZ 7) (literal_split128_low (@Word.zero 8 Alg.CoreFunSem tt))=0) in Low.
 change (@toZ (WordToZ 7) (literal_split128_high (@Word.zero 8 Alg.CoreFunSem tt))=0) in High.
 split;apply (toZ_injective (WordToZ 7));rewrite Word.zero_correct;assumption.
Qed.

Lemma literal_strauss_split128_zero :
 @literal_strauss_split128 Alg.CoreFunSem (@Word.zero 8 Alg.CoreFunSem tt)=
 (@literal_wnaf15 Alg.CoreFunSem (inl tt,@Word.zero 7 Alg.CoreFunSem tt),
  @literal_wnaf15 Alg.CoreFunSem (inl tt,@Word.zero 7 Alg.CoreFunSem tt)).
Proof.
 pose proof (literal_scalar_split128_step (@Word.zero 8 Alg.CoreFunSem tt)) as Split.
 assert (Pack:@literal_scalar_split128 Alg.CoreFunSem (@Word.zero 8 Alg.CoreFunSem tt)=
  ((inl tt,literal_split128_low (@Word.zero 8 Alg.CoreFunSem tt)),
   (inl tt,literal_split128_high (@Word.zero 8 Alg.CoreFunSem tt)))).
 { rewrite Split;reflexivity. }
 destruct strauss_split128_zero_halves as [Low High].
 rewrite Low,High in Pack.
 rewrite literal_strauss_split128_value.
 exact (f_equal (fun split=>
  (@literal_wnaf15 Alg.CoreFunSem (fst split),@literal_wnaf15 Alg.CoreFunSem (snd split))) Pack).
Qed.

Lemma strauss_zero_generator_wnaf_vectors :
 let '(head,tail):=@literal_wnaf15 Alg.CoreFunSem (inl tt,@Word.zero 7 Alg.CoreFunSem tt) in
 head=inl tt /\ literal_wnaf_flatten 7 tail=repeat (inl tt) 128.
Proof.
 pose proof (strauss_wnaf15_zero_digits (@Word.zero 7 Alg.CoreFunSem tt) (Word.zero_correct 7)) as Digits.
 unfold literal_wnaf15_digits in Digits.
 destruct (@literal_wnaf15 Alg.CoreFunSem (inl tt,@Word.zero 7 Alg.CoreFunSem tt)) as [head tail].
 change (head::literal_wnaf_flatten 7 tail=(inl tt)::repeat (inl tt) 128) in Digits.
 split.
 - exact (f_equal (fun xs:list (Ty.tySem literal_wnaf_digit)=>hd (inl tt) xs) Digits).
 - exact (f_equal (@tl (Ty.tySem literal_wnaf_digit)) Digits).
Qed.

Theorem strauss_wnaf5_short_loop_literal m b (state1 statelam:Ty.tySem literal_wnaf_state) sign1 signlam last1 lastlam digits1 digitslam
 (context:Ty.tySem literal_strauss_context) :
 wnaf_array_state m b 0 129 5 sign1 129 last1 digits1 ->
 wnaf_array_state m b 516 129 5 signlam 129 lastlam digitslam ->
 map wnaf5_literal_value (literal_wnaf5_digits state1)=
  rev (map (fun j=>sign1*digits1 (Z.of_nat j)) (seq 0 129)) ->
 map wnaf5_literal_value (literal_wnaf5_digits statelam)=
  rev (map (fun j=>signlam*digitslam (Z.of_nat j)) (seq 0 129)) ->
 strauss_scale_loop_result (Z.to_nat (Z.max (last1+1) (lastlam+1)))
  (strauss_wnaf5_digit_at state1) (strauss_wnaf5_digit_at statelam) context
  (@literal_gej_infinity Alg.CoreFunSem tt)=
 @literal_strauss_digits129 Alg.CoreFunSem
  (@literal_gej_infinity Alg.CoreFunSem tt,(context,
   ((@literal_wnaf5 Alg.CoreFunSem state1,@literal_wnaf5 Alg.CoreFunSem statelam),
    (@literal_wnaf15 Alg.CoreFunSem (inl tt,@Word.zero 7 Alg.CoreFunSem tt),
     @literal_wnaf15 Alg.CoreFunSem (inl tt,@Word.zero 7 Alg.CoreFunSem tt))))).
Proof.
 intros A1 AL L1 LL.
 destruct (strauss_wnaf5_array_for_loop m b 0 state1 digits1 sign1 last1 A1 L1) as [B1 D1].
 destruct (strauss_wnaf5_array_for_loop m b 516 statelam digitslam signlam lastlam AL LL) as [BL DL].
 pose proof (strauss_wnaf5_digit_at_vectors state1 statelam) as Digits.
 pose proof strauss_zero_generator_wnaf_vectors as Generator.
 destruct (@literal_wnaf5 Alg.CoreFunSem state1) as [h1 t1],
  (@literal_wnaf5 Alg.CoreFunSem statelam) as [hlam tlam].
 destruct (@literal_wnaf15 Alg.CoreFunSem (inl tt,@Word.zero 7 Alg.CoreFunSem tt)) as [hg tg].
 destruct Generator as [Head Tail];subst hg.
 apply strauss_scale_short_loop_literal129;[lia| |exact Digits|exact Tail|exact Tail].
 intros j [Lower Upper].
 assert (Range:0<=Z.of_nat j<129) by lia.
 assert (Above:Z.max (last1+1) (lastlam+1)<=Z.of_nat j).
 { apply Nat2Z.inj_le in Lower;rewrite Z2Nat.id in Lower by lia;exact Lower. }
 split;[apply (proj2 (D1 _ Range))|apply (proj2 (DL _ Range))];lia.
Qed.

Require Import C.jet_secp_generator_program C.jet_secp_generator_loop_literal C.jet_secp_double_literal.
Local Opaque literal_generator_step literal_generator_digits129 literal_gej_double.
Lemma strauss_generator_absent_fold n :
 fold_left (fun point pair=>@literal_generator_step Alg.CoreFunSem (point,pair))
  (repeat (inl tt,inl tt) n) (@literal_gej_infinity Alg.CoreFunSem tt)=
 @literal_gej_infinity Alg.CoreFunSem tt.
Proof.
 induction n as [|n IH];[reflexivity|].
 change (fold_left (fun point pair=>@literal_generator_step Alg.CoreFunSem (point,pair))
  (repeat (inl tt,inl tt) n)
  (@literal_generator_step Alg.CoreFunSem (@literal_gej_infinity Alg.CoreFunSem tt,(inl tt,inl tt)))=
 @literal_gej_infinity Alg.CoreFunSem tt).
 rewrite literal_generator_step_value,generator_double_infinity;exact IH.
Qed.

Lemma strauss_generate_zero :
 @literal_generate Alg.CoreFunSem (@Word.zero 8 Alg.CoreFunSem tt)=@literal_gej_infinity Alg.CoreFunSem tt.
Proof.
 rewrite literal_generate_value.
 destruct strauss_split128_zero_halves as [Low High];rewrite Low,High.
 pose proof strauss_zero_generator_wnaf_vectors as Zero.
 change (@literal_generator_digits129 Alg.CoreFunSem
  (@literal_gej_infinity Alg.CoreFunSem tt,
   (@literal_wnaf15 Alg.CoreFunSem (inl tt,@Word.zero 7 Alg.CoreFunSem tt),
    @literal_wnaf15 Alg.CoreFunSem (inl tt,@Word.zero 7 Alg.CoreFunSem tt)))=
  @literal_gej_infinity Alg.CoreFunSem tt).
 destruct (@literal_wnaf15 Alg.CoreFunSem (inl tt,@Word.zero 7 Alg.CoreFunSem tt)) as [head tail].
 destruct Zero as [Head Tail];subst head.
 rewrite literal_generator_digits129_list,Tail,strauss_combine_repeats.
 apply strauss_generator_absent_fold.
Qed.

Theorem strauss_scale_body_from_arrays m b (raw:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej)
 sign1 signlam last1 lastlam digits1 digitslam :
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 wnaf_array_state m b 0 129 5 sign1 129 last1 digits1 ->
 wnaf_array_state m b 516 129 5 signlam 129 lastlam digitslam ->
 map wnaf5_literal_value (literal_wnaf5_digits (fst halves))=
  rev (map (fun j=>sign1*digits1 (Z.of_nat j)) (seq 0 129)) ->
 map wnaf5_literal_value (literal_wnaf5_digits (snd halves))=
  rev (map (fun j=>signlam*digitslam (Z.of_nat j)) (seq 0 129)) ->
 let context:=@literal_scalar_table5 Alg.CoreFunSem point in
 let result:=strauss_scale_loop_result (Z.to_nat (Z.max (last1+1) (lastlam+1)))
  (strauss_wnaf5_digit_at (fst halves)) (strauss_wnaf5_digit_at (snd halves)) context
  (@literal_gej_infinity Alg.CoreFunSem tt) in
 (fst result,@literal_fe_multiply Alg.CoreFunSem (fst context,snd result))=
 @literal_strauss_body Alg.CoreFunSem ((raw,point),@Word.zero 8 Alg.CoreFunSem tt).
Proof.
 cbv zeta;intros A1 AL L1 LL.
 pose proof (strauss_wnaf5_short_loop_literal m b
  (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw))
  (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw))
  sign1 signlam last1 lastlam digits1 digitslam
  (@literal_scalar_table5 Alg.CoreFunSem point) A1 AL L1 LL) as Fold.
 symmetry;rewrite literal_strauss_body_value,literal_strauss_split_lambda_value,literal_strauss_split128_zero.
 exact (eq_sym (f_equal (fun result:Ty.tySem literal_table_gej=>
  (fst result,@literal_fe_multiply Alg.CoreFunSem
   (fst (@literal_scalar_table5 Alg.CoreFunSem point),snd result))) Fold)).
Qed.
