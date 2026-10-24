(** Literal port of Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:709--733.
    Constants follow the canonical FE computations in LibSecp256k1/Spec.hs,
    not the C constants; their agreement is checked below. This adapter is
    needed for the original C mapper proof, not standalone jet coverage. *)
From Coq Require Import ZArith Lia.
From Coqprime Require Import ZCAux.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_toZ C.jet_secp_swu_candidates
  C.jet_secp_decompress_literal C.jet_secp_canonical_odd C.jet_secp_gej_negate_literal
  C.jet_secp_gej_negate_parametric C.jet_secp_negate_literal_contract
  C.jet_secp_literal_add_program C.jet_secp_literal_infinity C.jet_secp_multiply_literal_spec
  C.jet_secp_square_execution C.jet_secp_rescale_literal C.jet_secp_curve_literal
  C.jet_secp_invert_literal C.jet_secp_eea_parametric C.jet_literal_division_parametric.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

(** FE exponentiation is modular; fe_halve adds p to an odd canonical value
    before integer division by two. Only closed modular powers are evaluated. *)
Definition swu_spec_c := Zpow_mod ((-3) mod feP) ((feP+1)/4) feP.
Definition swu_spec_d :=
  ((((swu_spec_c-1) mod feP)+(if Z.odd ((swu_spec_c-1) mod feP) then feP else 0))/2) mod feP.
Lemma swu_spec_c_value : swu_spec_c=swu_c_constant.
Proof. unfold swu_spec_c,swu_c_constant,swu_negc_constant;vm_compute;reflexivity. Qed.
Lemma swu_spec_d_value : swu_spec_d=swu_d_constant.
Proof.
  unfold swu_spec_d;rewrite swu_spec_c_value;
    unfold swu_c_constant,swu_negc_constant,swu_d_constant;vm_compute;reflexivity.
Qed.
Lemma swu_spec_negc_value : (-swu_spec_c) mod feP=swu_negc_constant.
Proof. rewrite swu_spec_c_value;unfold swu_c_constant,swu_negc_constant;vm_compute;reflexivity. Qed.

Definition swu_scribe256 (z:Z) {term:Alg.Core.Algebra} {A:Ty.Ty} : term A (Word 8) :=
  Alg.scribe (@fromZ (WordToZ 8) z).
Definition literal_swu_candidates {term:Alg.Core.Algebra} :
  term (Word 8) (Ty.Prod (Word 8) (Word 8)) :=
  @literal_fe_square term >>>
  (iden &&& @swu_scribe256 ((-swu_spec_c) mod feP) term _ >>> @literal_fe_multiply term) &&&
  (iden &&& @swu_scribe256 8 term _ >>> @literal_fe_add term) &&&
  (iden &&& @swu_scribe256 3 term _ >>> @literal_fe_multiply term) >>>
  (iden &&& (I (@literal_fe_multiply term) >>> @literal_fe_invert term)) >>>
  ((O (O H) &&& (O (I (I H)) &&& I H >>> @literal_fe_multiply term)
      >>> @literal_fe_multiply term) &&& @swu_scribe256 swu_spec_d term _
    >>> @literal_fe_add term) &&&
  ((O (I (O (@literal_fe_cube term))) &&& I (@literal_fe_negate term)
      >>> @literal_fe_multiply term) &&& (unit >>> @literal_fe_one256 term)
    >>> @literal_fe_add term).

(** Haskell's flip match success failure is case failure success. Retain the
    third failure branch; the execution bridge must prove it unreachable. *)
Definition literal_swu_select {term:Alg.Core.Algebra} :
  term (Ty.Prod (Word 8) (Word 8)) (Ty.Prod (Word 8) (Word 8)) :=
  (O (@literal_y_from_x term) &&& iden) >>>
  case
    (I (((O H &&& (unit >>> @literal_fe_one256 term) >>> @literal_fe_add term
       >>> @literal_fe_negate term) &&& I H)) >>>
      (O (@literal_y_from_x term) &&& iden) >>>
      case
        (I (I (@literal_y_from_x term &&& iden) >>>
          case (unit >>> (@literal_fe_zero256 term &&& @literal_fe_zero256 term)) (I H &&& O H)))
        (I (O H) &&& O H))
    (I (O H) &&& O H).
Definition literal_swu {term:Alg.Core.Algebra} :
  term (Word 8) (Ty.Prod (Word 8) (Word 8)) :=
  (** Keep this source prefix inline. Composing the auxiliary candidate term
      with select would reassociate the original right-associated tree. *)
  (@canonical_fe_is_odd term &&&
   (@literal_fe_square term >>>
    (iden &&& @swu_scribe256 ((-swu_spec_c) mod feP) term _ >>> @literal_fe_multiply term) &&&
    (iden &&& @swu_scribe256 8 term _ >>> @literal_fe_add term) &&&
    (iden &&& @swu_scribe256 3 term _ >>> @literal_fe_multiply term) >>>
    (iden &&& (I (@literal_fe_multiply term) >>> @literal_fe_invert term)) >>>
    ((O (O H) &&& (O (I (I H)) &&& I H >>> @literal_fe_multiply term)
        >>> @literal_fe_multiply term) &&& @swu_scribe256 swu_spec_d term _
      >>> @literal_fe_add term) &&&
    ((O (I (O (@literal_fe_cube term))) &&& I (@literal_fe_negate term)
        >>> @literal_fe_multiply term) &&& (unit >>> @literal_fe_one256 term)
      >>> @literal_fe_add term) >>> @literal_swu_select term))
  >>> Bit.cond (@literal_ge_negate term) iden.

Lemma swu_scribe256_parametric z A :
  Alg.Core.Parametric (fun term=>@swu_scribe256 z term A).
Proof. intros t1 t2 R;unfold swu_scribe256;apply Alg.scribe_Parametric. Qed.
Lemma literal_swu_candidates_parametric : Alg.Core.Parametric (@literal_swu_candidates).
Proof.
  intros t1 t2 R;unfold literal_swu_candidates.
  repeat first [apply swu_scribe256_parametric|apply curve_square_parametric|
    apply literal_fe_multiply_parametric|apply literal_fe_add_parametric|
    apply literal_fe_negate_parametric|apply literal_fe_invert_parametric|
    apply curve_cube_parametric|apply literal_fe_one256_parametric|
    apply Alg.comp_Parametric|apply Alg.pair_Parametric|apply Alg.take_Parametric|
    apply Alg.drop_Parametric|apply Alg.iden_Parametric|apply Alg.unit_Parametric].
Qed.
Lemma literal_swu_select_parametric : Alg.Core.Parametric (@literal_swu_select).
Proof.
  intros t1 t2 R;unfold literal_swu_select.
  repeat first [apply literal_y_from_x_parametric|apply literal_fe_add_parametric|
    apply literal_fe_negate_parametric|apply literal_fe_one256_parametric|
    apply literal_fe_zero256_parametric|apply Alg.comp_Parametric|apply Alg.pair_Parametric|
    apply Alg.take_Parametric|apply Alg.drop_Parametric|apply Alg.case_Parametric|
    apply Alg.iden_Parametric|apply Alg.unit_Parametric].
Qed.
Lemma literal_swu_parametric : Alg.Core.Parametric (@literal_swu).
Proof.
  intros t1 t2 R;unfold literal_swu.
  repeat first [apply swu_scribe256_parametric|apply curve_square_parametric|
    apply literal_fe_multiply_parametric|apply literal_fe_add_parametric|
    apply literal_fe_negate_parametric|apply literal_fe_invert_parametric|
    apply curve_cube_parametric|apply literal_fe_one256_parametric|apply literal_swu_select_parametric|
    apply decompress_odd_parametric|apply literal_ge_negate_parametric|apply Bit.cond_Parametric|
    apply Alg.comp_Parametric|apply Alg.pair_Parametric|apply Alg.take_Parametric|
    apply Alg.drop_Parametric|apply Alg.iden_Parametric|apply Alg.unit_Parametric].
Qed.

Local Opaque literal_fe_square literal_fe_multiply literal_fe_add literal_fe_cube
  literal_fe_invert literal_fe_negate literal_fe_one256 literal_fe_zero256
  canonical_fe_is_odd literal_y_from_x literal_ge_negate fromZ swu_spec_c swu_spec_d.
Lemma literal_swu_candidates_step (t:Ty.tySem (Word 8)) :
  let s:=@literal_fe_square Alg.CoreFunSem t in
  let a:=@literal_fe_multiply Alg.CoreFunSem
    (s,@fromZ (WordToZ 8) ((-swu_spec_c) mod feP)) in
  let w:=@literal_fe_add Alg.CoreFunSem (s,@fromZ (WordToZ 8) 8) in
  let b:=@literal_fe_multiply Alg.CoreFunSem (s,@fromZ (WordToZ 8) 3) in
  let i:=@literal_fe_invert Alg.CoreFunSem (@literal_fe_multiply Alg.CoreFunSem (w,b)) in
  @literal_swu_candidates Alg.CoreFunSem t=
  (@literal_fe_add Alg.CoreFunSem
    (@literal_fe_multiply Alg.CoreFunSem (a,@literal_fe_multiply Alg.CoreFunSem (b,i)),
      @fromZ (WordToZ 8) swu_spec_d),
   @literal_fe_add Alg.CoreFunSem
    (@literal_fe_multiply Alg.CoreFunSem (@literal_fe_cube Alg.CoreFunSem w,
      @literal_fe_negate Alg.CoreFunSem i),@literal_fe_one256 Alg.CoreFunSem tt)).
Proof.
  unfold literal_swu_candidates;
    cbn -[swu_scribe256 literal_fe_square literal_fe_multiply literal_fe_add literal_fe_cube
      literal_fe_invert literal_fe_negate literal_fe_one256 fromZ swu_spec_c swu_spec_d].
  unfold swu_scribe256;rewrite !Alg.scribe_correct;reflexivity.
Qed.
Lemma literal_swu_select_step (x1 x3:Ty.tySem (Word 8)) :
  @literal_swu_select Alg.CoreFunSem (x1,x3)=
  match @literal_y_from_x Alg.CoreFunSem x1 with
  | inr y=>(x1,y)
  | inl _=>let x2:=@literal_fe_negate Alg.CoreFunSem
      (@literal_fe_add Alg.CoreFunSem (x1,@literal_fe_one256 Alg.CoreFunSem tt)) in
    match @literal_y_from_x Alg.CoreFunSem x2 with
    | inr y=>(x2,y)
    | inl _=>match @literal_y_from_x Alg.CoreFunSem x3 with
      | inr y=>(x3,y)
      | inl _=>(@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt)
      end
    end
  end.
Proof. unfold literal_swu_select;reflexivity. Qed.
Lemma literal_swu_step (t:Ty.tySem (Word 8)) :
  @literal_swu Alg.CoreFunSem t=
  let p:=@literal_swu_select Alg.CoreFunSem (@literal_swu_candidates Alg.CoreFunSem t) in
  if Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem t)
    then @literal_ge_negate Alg.CoreFunSem p else p.
Proof.
  change ((match @canonical_fe_is_odd Alg.CoreFunSem t with
    | inl _=>@literal_swu_select Alg.CoreFunSem (@literal_swu_candidates Alg.CoreFunSem t)
    | inr _=>@literal_ge_negate Alg.CoreFunSem
        (@literal_swu_select Alg.CoreFunSem (@literal_swu_candidates Alg.CoreFunSem t))
    end)=
    if Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem t)
      then @literal_ge_negate Alg.CoreFunSem
        (@literal_swu_select Alg.CoreFunSem (@literal_swu_candidates Alg.CoreFunSem t))
      else @literal_swu_select Alg.CoreFunSem (@literal_swu_candidates Alg.CoreFunSem t)).
  destruct (@canonical_fe_is_odd Alg.CoreFunSem t) as [u|u];destruct u;reflexivity.
Qed.
