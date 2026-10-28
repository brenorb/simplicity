(** Four-stream loop order against the literal 129-step Simplicity program. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_secp_strauss_general_loop C.jet_secp_strauss_program
 C.jet_secp_scalar_table_literal C.jet_secp_wnaf5_literal C.jet_secp_wnaf_literal
 C.jet_secp_strauss_scale_loop C.jet_secp_generator_loop_literal
 C.jet_secp_double_literal C.jet_secp_literal_infinity.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_strauss_step literal_gej_double literal_gej_infinity.

Lemma strauss_general_loop_result_fold count digits1 digitslam digitsg1 digitsg128 context point :
 strauss_general_loop_result count digits1 digitslam digitsg1 digitsg128 context point=
 fold_left (fun point ds=>@literal_strauss_step Alg.CoreFunSem (point,(context,ds)))
  (map (fun j=>((digits1 (Z.of_nat j),digitslam (Z.of_nat j)),
   (digitsg1 (Z.of_nat j),digitsg128 (Z.of_nat j)))) (rev (seq 0 count))) point.
Proof.
 revert point;induction count as [|count IH];intro point;[reflexivity|].
 cbn [strauss_general_loop_result];rewrite IH,seq_S,rev_app_distr,map_app.
 cbn [rev app map fold_left Nat.add];reflexivity.
Qed.

Theorem strauss_general_remove_leading_zeros count keep digits1 digitslam digitsg1 digitsg128 context :
 (keep<=count)%nat ->
 (forall j,(keep<=j<count)%nat -> digits1 (Z.of_nat j)=inl tt /\ digitslam (Z.of_nat j)=inl tt /\
  digitsg1 (Z.of_nat j)=inl tt /\ digitsg128 (Z.of_nat j)=inl tt) ->
 strauss_general_loop_result count digits1 digitslam digitsg1 digitsg128 context (@literal_gej_infinity Alg.CoreFunSem tt)=
 strauss_general_loop_result keep digits1 digitslam digitsg1 digitsg128 context (@literal_gej_infinity Alg.CoreFunSem tt).
Proof.
 induction count as [|count IH];intros Bound Zeros.
 - assert (Eq:keep=0%nat) by lia;subst keep;reflexivity.
 - destruct (Nat.eq_dec keep (S count)) as [Eq|Different];[rewrite Eq;reflexivity|].
   destruct (Zeros count ltac:(lia)) as (D1 & DL & G1 & G128).
   change (strauss_general_loop_result count digits1 digitslam digitsg1 digitsg128 context
    (@literal_strauss_step Alg.CoreFunSem
     (@literal_gej_infinity Alg.CoreFunSem tt,(context,
      ((digits1 (Z.of_nat count),digitslam (Z.of_nat count)),
       (digitsg1 (Z.of_nat count),digitsg128 (Z.of_nat count))))))=
    strauss_general_loop_result keep digits1 digitslam digitsg1 digitsg128 context (@literal_gej_infinity Alg.CoreFunSem tt)).
   rewrite D1,DL,G1,G128,strauss_scale_step_absent,generator_double_infinity.
   apply IH;[lia|intros j Range;apply Zeros;lia].
Qed.

Theorem strauss_general_loop_literal129 digits1 digitslam digitsg1 digitsg128
 (point:Ty.tySem literal_table_gej) (context:Ty.tySem literal_strauss_context)
 (h1:Ty.tySem literal_wnaf5_digit) (t1:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hlam:Ty.tySem literal_wnaf5_digit) (tlam:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hg1:Ty.tySem literal_wnaf_digit) (tg1:Ty.tySem (Vector literal_wnaf_digit 7))
 (hg128:Ty.tySem literal_wnaf_digit) (tg128:Ty.tySem (Vector literal_wnaf_digit 7)) :
 map (fun j=>((digits1 (Z.of_nat j),digitslam (Z.of_nat j)),
  (digitsg1 (Z.of_nat j),digitsg128 (Z.of_nat j)))) (rev (seq 0 129))=
  ((h1,hlam),(hg1,hg128))::
   combine (combine (literal_wnaf5_flatten 7 t1) (literal_wnaf5_flatten 7 tlam))
    (combine (literal_wnaf_flatten 7 tg1) (literal_wnaf_flatten 7 tg128)) ->
 strauss_general_loop_result 129 digits1 digitslam digitsg1 digitsg128 context point=
 @literal_strauss_digits129 Alg.CoreFunSem
  (point,(context,(((h1,t1),(hlam,tlam)),((hg1,tg1),(hg128,tg128))))).
Proof.
 intro Digits;rewrite strauss_general_loop_result_fold,Digits,literal_strauss_digits129_list;reflexivity.
Qed.

Theorem strauss_general_short_loop_literal129 keep digits1 digitslam digitsg1 digitsg128
 (context:Ty.tySem literal_strauss_context)
 (h1:Ty.tySem literal_wnaf5_digit) (t1:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hlam:Ty.tySem literal_wnaf5_digit) (tlam:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hg1:Ty.tySem literal_wnaf_digit) (tg1:Ty.tySem (Vector literal_wnaf_digit 7))
 (hg128:Ty.tySem literal_wnaf_digit) (tg128:Ty.tySem (Vector literal_wnaf_digit 7)) :
 (keep<=129)%nat ->
 (forall j,(keep<=j<129)%nat -> digits1 (Z.of_nat j)=inl tt /\ digitslam (Z.of_nat j)=inl tt /\
  digitsg1 (Z.of_nat j)=inl tt /\ digitsg128 (Z.of_nat j)=inl tt) ->
 map (fun j=>((digits1 (Z.of_nat j),digitslam (Z.of_nat j)),
  (digitsg1 (Z.of_nat j),digitsg128 (Z.of_nat j)))) (rev (seq 0 129))=
  ((h1,hlam),(hg1,hg128))::
   combine (combine (literal_wnaf5_flatten 7 t1) (literal_wnaf5_flatten 7 tlam))
    (combine (literal_wnaf_flatten 7 tg1) (literal_wnaf_flatten 7 tg128)) ->
 strauss_general_loop_result keep digits1 digitslam digitsg1 digitsg128 context (@literal_gej_infinity Alg.CoreFunSem tt)=
 @literal_strauss_digits129 Alg.CoreFunSem
  (@literal_gej_infinity Alg.CoreFunSem tt,(context,(((h1,t1),(hlam,tlam)),((hg1,tg1),(hg128,tg128))))).
Proof.
 intros Bound Zeros Digits.
 rewrite <-(strauss_general_remove_leading_zeros 129 keep digits1 digitslam digitsg1 digitsg128 context Bound Zeros).
 apply strauss_general_loop_literal129;exact Digits.
Qed.
