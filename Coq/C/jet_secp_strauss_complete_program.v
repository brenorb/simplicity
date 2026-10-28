(** Complete literal off_curve_linear_combination_1 and off_curve_scale
    routing from frozen LibSecp256k1.hs:628--672. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_secp_strauss_program C.jet_secp_scalar_table_literal
 C.jet_secp_split_literal C.jet_secp_scalar_split128_literal
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf_literal C.jet_secp_literal_infinity
 C.jet_secp_literal_gej_predicate C.jet_secp_canonical_scalar_zero
 C.jet_secp_generate_program C.jet_secp_negate_literal_contract.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_strauss_args :=
 Ty.Prod (Ty.Prod (Word 8) literal_table_gej) (Word 8).
Definition strauss_split_windows {term:Alg.Core.Algebra} (digit:Ty.Ty)
 (split:term (Word 8) (Ty.Prod literal_wnaf_state literal_wnaf_state))
 (wnaf:term literal_wnaf_state (Ty.Prod digit (Vector digit 7))) :
 term (Word 8) (Ty.Prod (Ty.Prod digit (Vector digit 7)) (Ty.Prod digit (Vector digit 7))) :=
 split >>> (O wnaf &&& I wnaf).
Definition literal_strauss_split_lambda {term:Alg.Core.Algebra} :
 term (Word 8) (Ty.Prod
  (Ty.Prod literal_wnaf5_digit (Vector literal_wnaf5_digit 7))
  (Ty.Prod literal_wnaf5_digit (Vector literal_wnaf5_digit 7))) :=
 @strauss_split_windows term literal_wnaf5_digit (@literal_scalar_split_lambda term) (@literal_wnaf5 term).
Definition literal_strauss_split128 {term:Alg.Core.Algebra} :
 term (Word 8) (Ty.Prod
  (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))
  (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))) :=
 @strauss_split_windows term literal_wnaf_digit (@literal_scalar_split128 term) (@literal_wnaf15 term).
Definition strauss_body_routing {term:Alg.Core.Algebra}
 (infinity:term Ty.Unit literal_table_gej)
 (table:term literal_table_gej literal_strauss_context)
 (splitlam:term (Word 8) (Ty.Prod
  (Ty.Prod literal_wnaf5_digit (Vector literal_wnaf5_digit 7))
  (Ty.Prod literal_wnaf5_digit (Vector literal_wnaf5_digit 7))))
 (splitgen:term (Word 8) (Ty.Prod
  (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))
  (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))))
 (digits:term (literal_strauss_input
  (Ty.Prod literal_wnaf5_digit (Vector literal_wnaf5_digit 7))
  (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))) literal_table_gej)
 (multiply:term (Ty.Prod (Word 8) (Word 8)) (Word 8)) :
 term literal_strauss_args literal_table_gej :=
 ((unit >>> infinity) &&& (O I H >>> table)
  &&& (O O H >>> splitlam) &&& (I H >>> splitgen))
 >>> (I O O H &&& digits) >>> (I O H &&& ((O H &&& I I H) >>> multiply)).
Definition literal_strauss_body {term:Alg.Core.Algebra} : term literal_strauss_args literal_table_gej :=
 @strauss_body_routing term (@literal_gej_infinity term) (@literal_scalar_table5 term)
  (@literal_strauss_split_lambda term) (@literal_strauss_split128 term)
  (@literal_strauss_digits129 term) (@literal_fe_multiply term).
Definition literal_strauss_guard {term:Alg.Core.Algebra} : term literal_strauss_args Bit :=
 Bit.or (O (I (@literal_gej_is_infinity term))) (O (O (@canonical_scalar_is_zero term))).
Definition literal_off_curve_linear_combination_1 {term:Alg.Core.Algebra} :
 term literal_strauss_args literal_table_gej :=
 (@literal_strauss_guard term &&& iden) >>>
 Bit.cond (I (@literal_generate term)) (@literal_strauss_body term).
Definition literal_off_curve_scale {term:Alg.Core.Algebra} :
 term (Ty.Prod (Word 8) literal_table_gej) literal_table_gej :=
 (iden &&& (unit >>> @Word.zero 8 term)) >>> @literal_off_curve_linear_combination_1 term.

Local Opaque literal_scalar_table5 literal_scalar_split_lambda literal_scalar_split128
 literal_wnaf5 literal_wnaf15 literal_gej_infinity literal_strauss_digits129 literal_fe_multiply
 literal_gej_is_infinity canonical_scalar_is_zero literal_generate Word.zero.

Lemma strauss_split_windows_value (digit:Ty.Ty)
 (split:Ty.tySem (Word 8) -> Ty.tySem (Ty.Prod literal_wnaf_state literal_wnaf_state))
 (wnaf:Ty.tySem literal_wnaf_state -> Ty.tySem (Ty.Prod digit (Vector digit 7)))
 (raw:Ty.tySem (Word 8)) :
 @strauss_split_windows Alg.CoreFunSem digit split wnaf raw=
 (wnaf (fst (split raw)),wnaf (snd (split raw))).
Proof. reflexivity. Qed.

Lemma literal_strauss_split_lambda_value (raw:Ty.tySem (Word 8)) :
 @literal_strauss_split_lambda Alg.CoreFunSem raw=
 (@literal_wnaf5 Alg.CoreFunSem (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)),
  @literal_wnaf5 Alg.CoreFunSem (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw))).
Proof. apply strauss_split_windows_value. Qed.
Lemma literal_strauss_split128_value (raw:Ty.tySem (Word 8)) :
 @literal_strauss_split128 Alg.CoreFunSem raw=
 (@literal_wnaf15 Alg.CoreFunSem (fst (@literal_scalar_split128 Alg.CoreFunSem raw)),
  @literal_wnaf15 Alg.CoreFunSem (snd (@literal_scalar_split128 Alg.CoreFunSem raw))).
Proof. apply strauss_split_windows_value. Qed.

Lemma strauss_body_routing_value
 (infinity:Ty.tySem Ty.Unit -> Ty.tySem literal_table_gej)
 (table:Ty.tySem literal_table_gej -> Ty.tySem literal_strauss_context)
 (splitlam:Ty.tySem (Word 8) -> Ty.tySem (Ty.Prod
  (Ty.Prod literal_wnaf5_digit (Vector literal_wnaf5_digit 7))
  (Ty.Prod literal_wnaf5_digit (Vector literal_wnaf5_digit 7))))
 (splitgen:Ty.tySem (Word 8) -> Ty.tySem (Ty.Prod
  (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))
  (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))))
 (digits:Ty.tySem (literal_strauss_input
  (Ty.Prod literal_wnaf5_digit (Vector literal_wnaf5_digit 7))
  (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))) -> Ty.tySem literal_table_gej)
 (multiply:Ty.tySem (Ty.Prod (Word 8) (Word 8)) -> Ty.tySem (Word 8))
 (raw:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej) (ng:Ty.tySem (Word 8)) :
 @strauss_body_routing Alg.CoreFunSem infinity table splitlam splitgen digits multiply ((raw,point),ng)=
 let context:=table point in
 let result:=digits (infinity tt,(context,(splitlam raw,splitgen ng))) in
 (fst result,multiply (fst context,snd result)).
Proof. reflexivity. Qed.

Lemma literal_strauss_body_value (raw:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej) (ng:Ty.tySem (Word 8)) :
 @literal_strauss_body Alg.CoreFunSem ((raw,point),ng)=
 let context:=@literal_scalar_table5 Alg.CoreFunSem point in
 let result:=@literal_strauss_digits129 Alg.CoreFunSem
  (@literal_gej_infinity Alg.CoreFunSem tt,(context,
   (@literal_strauss_split_lambda Alg.CoreFunSem raw,@literal_strauss_split128 Alg.CoreFunSem ng))) in
 (fst result,@literal_fe_multiply Alg.CoreFunSem (fst context,snd result)).
Proof. apply strauss_body_routing_value. Qed.

Lemma literal_strauss_guard_value (raw:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej) (ng:Ty.tySem (Word 8)) :
 Bit.toBool (@literal_strauss_guard Alg.CoreFunSem ((raw,point),ng))=
 orb (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem point))
  (Bit.toBool (@canonical_scalar_is_zero Alg.CoreFunSem raw)).
Proof.
 change (Bit.toBool (match @literal_gej_is_infinity Alg.CoreFunSem point with
  | inl _=>@canonical_scalar_is_zero Alg.CoreFunSem raw | inr _=>inr tt end)=
 orb (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem point))
  (Bit.toBool (@canonical_scalar_is_zero Alg.CoreFunSem raw))).
 destruct (@literal_gej_is_infinity Alg.CoreFunSem point) as [u|u];destruct u;reflexivity.
Qed.

Local Opaque literal_strauss_body literal_strauss_guard.
Lemma literal_off_curve_linear_combination_1_value (raw:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej) (ng:Ty.tySem (Word 8)) :
 @literal_off_curve_linear_combination_1 Alg.CoreFunSem ((raw,point),ng)=
 if Bit.toBool (@literal_strauss_guard Alg.CoreFunSem ((raw,point),ng))
 then @literal_generate Alg.CoreFunSem ng
 else @literal_strauss_body Alg.CoreFunSem ((raw,point),ng).
Proof.
 change ((match @literal_strauss_guard Alg.CoreFunSem ((raw,point),ng) with
 | inl _=>@literal_strauss_body Alg.CoreFunSem ((raw,point),ng)
 | inr _=>@literal_generate Alg.CoreFunSem ng end)=
 if Bit.toBool (@literal_strauss_guard Alg.CoreFunSem ((raw,point),ng))
 then @literal_generate Alg.CoreFunSem ng
 else @literal_strauss_body Alg.CoreFunSem ((raw,point),ng)).
 destruct (@literal_strauss_guard Alg.CoreFunSem ((raw,point),ng)) as [u|u];destruct u;reflexivity.
Qed.

Lemma literal_off_curve_scale_value (raw:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej) :
 @literal_off_curve_scale Alg.CoreFunSem (raw,point)=
 @literal_off_curve_linear_combination_1 Alg.CoreFunSem
  ((raw,point),@Word.zero 8 Alg.CoreFunSem tt).
Proof. reflexivity. Qed.
