(** Identify the proved C loop result with the canonical generate step fold;
    retain the digit representation relation as an internal caller obligation. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_secp_generate_literal C.jet_secp_wnaf_literal
 C.jet_secp_generator_iteration C.jet_secp_generator_loop C.jet_secp_double_literal
 C.jet_secp_add_literal C.jet_secp_literal_infinity C.jet_secp_literal_gej_predicate
 C.jet_secp_canonical_zero C.jet_secp_curve_literal C.jet_secp_fe_math.
Require Import C.jet_secp_generator_program.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque generator_digit_action literal_generator_step literal_gej_double literal_gej_infinity.

Lemma generator_step_matches_program point d1 d128 :
 generator_digit_action true d128 (generator_digit_action false d1
   (@literal_gej_double Alg.CoreFunSem point))=
 @literal_generator_step Alg.CoreFunSem (point,(d1,d128)).
Proof. rewrite literal_generator_step_value;destruct d1,d128;reflexivity. Qed.

Theorem generator_loop_result_fold count ds1 ds128 point :
 generator_loop_result count ds1 ds128 point=
 fold_left (fun point pair=>@literal_generator_step Alg.CoreFunSem (point,pair))
   (map (fun j=>(ds1 (Z.of_nat j),ds128 (Z.of_nat j))) (rev (seq 0 count))) point.
Proof.
 revert point;induction count as [|count IH];intro point;[reflexivity|].
 cbn [generator_loop_result];rewrite IH,seq_S,rev_app_distr,map_app.
 cbn [rev app map fold_left Nat.add];rewrite generator_step_matches_program;reflexivity.
Qed.

Theorem generator_loop_result_literal129 ds1 ds128 point head1 tail1 head128 tail128 :
 map (fun j=>(ds1 (Z.of_nat j),ds128 (Z.of_nat j))) (rev (seq 0 129))=
   (head1,head128)::combine (literal_wnaf_flatten 7 tail1) (literal_wnaf_flatten 7 tail128) ->
 generator_loop_result 129 ds1 ds128 point=
 @literal_generator_digits129 Alg.CoreFunSem (point,((head1,tail1),(head128,tail128))).
Proof.
 intro Digits;rewrite generator_loop_result_fold,Digits,literal_generator_digits129_list;reflexivity.
Qed.

Lemma generator_double_infinity :
 @literal_gej_double Alg.CoreFunSem (@literal_gej_infinity Alg.CoreFunSem tt)=
 @literal_gej_infinity Alg.CoreFunSem tt.
Proof.
 change (@literal_gej_double Alg.CoreFunSem
   ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),@literal_fe_zero256 Alg.CoreFunSem tt)=
   @literal_gej_infinity Alg.CoreFunSem tt).
 rewrite literal_gej_double_step,literal_gej_is_infinity_value,literal_curve_zero_numeric.
 assert (Zero : @toZ (WordToZ 8) (@literal_fe_zero256 Alg.CoreFunSem tt)=0).
 { unfold literal_fe_zero256;apply Word.zero_correct. }
 rewrite Zero;reflexivity.
Qed.

Theorem generator_loop_remove_leading_zeros count keep ds1 ds128 :
 (keep<=count)%nat ->
 (forall j,(keep<=j<count)%nat -> ds1 (Z.of_nat j)=inl tt /\ ds128 (Z.of_nat j)=inl tt) ->
 generator_loop_result count ds1 ds128 (@literal_gej_infinity Alg.CoreFunSem tt)=
 generator_loop_result keep ds1 ds128 (@literal_gej_infinity Alg.CoreFunSem tt).
Proof.
 induction count as [|count IH];intros Range Zeros.
 - assert (keep=0%nat) by lia;subst keep;reflexivity.
 - destruct (Nat.eq_dec keep (S count)) as [Equal|Different];[rewrite Equal;reflexivity|].
   destruct (Zeros count ltac:(lia)) as [Low High].
   cbn [generator_loop_result];rewrite Low,High.
   change (generator_loop_result count ds1 ds128 (@literal_gej_double Alg.CoreFunSem
     (@literal_gej_infinity Alg.CoreFunSem tt))=
     generator_loop_result keep ds1 ds128 (@literal_gej_infinity Alg.CoreFunSem tt)).
   rewrite generator_double_infinity;apply IH;[lia|intros j Bounds;apply Zeros;lia].
Qed.

Theorem generator_short_loop_literal129 keep ds1 ds128 head1 tail1 head128 tail128 :
 (keep<=129)%nat ->
 (forall j,(keep<=j<129)%nat -> ds1 (Z.of_nat j)=inl tt /\ ds128 (Z.of_nat j)=inl tt) ->
 map (fun j=>(ds1 (Z.of_nat j),ds128 (Z.of_nat j))) (rev (seq 0 129))=
   (head1,head128)::combine (literal_wnaf_flatten 7 tail1) (literal_wnaf_flatten 7 tail128) ->
 generator_loop_result keep ds1 ds128 (@literal_gej_infinity Alg.CoreFunSem tt)=
 @literal_generator_digits129 Alg.CoreFunSem
   (@literal_gej_infinity Alg.CoreFunSem tt,((head1,tail1),(head128,tail128))).
Proof.
 intros Bound Zeros Digits.
 rewrite <-(generator_loop_remove_leading_zeros 129 keep ds1 ds128 Bound Zeros).
 apply generator_loop_result_literal129;exact Digits.
Qed.
