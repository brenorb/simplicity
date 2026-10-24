(** Connect the exact literal SWU term to the original C candidate formulas.
    In particular, discharge the literal third-root-success obligation for
    every input. Actual C execution and serialization remain separate. *)
From Coq Require Import ZArith Lia Ring Morphisms Setoid.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_swu_literal C.jet_secp_swu_candidates C.jet_secp_swu_root_power
  C.jet_secp_swu_selection C.jet_secp_fe_math C.jet_toZ C.jet_word_repr
  C.jet_secp_decompress_literal C.jet_secp_canonical_odd C.jet_secp_canonical_normalize
  C.jet_secp_gej_negate_literal C.jet_secp_negate_literal_contract
  C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric C.jet_secp_literal_infinity
  C.jet_secp_multiply_literal_spec C.jet_secp_square_execution C.jet_secp_rescale_literal
  C.jet_secp_curve_literal C.jet_secp_invert_literal C.jet_secp_invert_modinv
  C.jet_secp_root_check C.jet_secp_root_chain_numeric C.jet_secp_root_literal C.modinv.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_swu_candidates literal_swu_select literal_fe_square literal_fe_multiply
  literal_fe_add literal_fe_cube literal_fe_invert literal_fe_negate literal_fe_one256
  literal_fe_zero256 canonical_fe_is_odd literal_y_from_x literal_ge_negate fromZ
  swu_spec_c swu_spec_d literal_root_candidate literal_root_check literal_fe_square_root.

Lemma swu_literal_multiply_match x y a b :
  eqm feP (@toZ (WordToZ 8) x) a -> eqm feP (@toZ (WordToZ 8) y) b ->
  eqm feP (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem (x,y))) (a*b).
Proof.
  intros X Y;unfold eqm;rewrite literal_multiply_numeric,Z.mod_mod by (unfold feP,feR;lia).
  apply (Zmult_eqm feP);assumption.
Qed.
Lemma swu_literal_add_match x y a b :
  eqm feP (@toZ (WordToZ 8) x) a -> eqm feP (@toZ (WordToZ 8) y) b ->
  eqm feP (@toZ (WordToZ 8) (@literal_fe_add Alg.CoreFunSem (x,y))) (a+b).
Proof.
  intros X Y;unfold eqm;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model,
    Z.mod_mod by (unfold feP,feR;lia);apply (Zplus_eqm feP);assumption.
Qed.
Lemma swu_literal_square_match x a : eqm feP (@toZ (WordToZ 8) x) a ->
  eqm feP (@toZ (WordToZ 8) (@literal_fe_square Alg.CoreFunSem x)) (a*a).
Proof.
  intro X;unfold eqm;rewrite literal_square_numeric,Z.mod_mod by (unfold feP,feR;lia).
  apply (Zmult_eqm feP);assumption.
Qed.
Lemma swu_literal_cube_match x a : eqm feP (@toZ (WordToZ 8) x) a ->
  eqm feP (@toZ (WordToZ 8) (@literal_fe_cube Alg.CoreFunSem x)) (a*a*a).
Proof.
  intro X;unfold eqm;rewrite literal_curve_cube_numeric,Z.mod_mod by (unfold feP,feR;lia).
  apply (Zmult_eqm feP);[apply (Zmult_eqm feP);assumption|assumption].
Qed.
Lemma swu_literal_negate_match x a : eqm feP (@toZ (WordToZ 8) x) a ->
  eqm feP (@toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem x)) (-a).
Proof.
  intro X;unfold eqm;rewrite literal_curve_negate_numeric,Z.mod_mod by (unfold feP,feR;lia).
  replace (feP-@toZ (WordToZ 8) x) with (-@toZ (WordToZ 8) x+1*feP) by ring.
  rewrite Z.mod_add by (unfold feP,feR;lia);apply (Zopp_eqm feP);exact X.
Qed.
Lemma swu_literal_inverse_match x a : eqm feP (@toZ (WordToZ 8) x) a ->
  eqm feP (@toZ (WordToZ 8) (@literal_fe_invert Alg.CoreFunSem x)) (swu_inv a).
Proof.
  intro X;unfold eqm,swu_inv;rewrite literal_fe_invert_numeric,literal_invert_numeric_modInv
    by (apply word_toZ_range).
  rewrite (modInv_eqm feP _ _ X);reflexivity.
Qed.
Lemma swu_fromZ_match z : 0<=z<2^256 ->
  eqm feP (@toZ (WordToZ 8) (@fromZ (WordToZ 8) z)) z.
Proof.
  intro Bounds;unfold eqm;rewrite to_fromZ,two_power_nat_equiv,word_bitSize.
  change (Z.of_nat (2^8)) with 256.
  rewrite (Z.mod_small z (2^256) Bounds);reflexivity.
Qed.
Lemma swu_one_match :
  eqm feP (@toZ (WordToZ 8) (@literal_fe_one256 Alg.CoreFunSem tt)) 1.
Proof. unfold eqm;rewrite literal_fe_one256_value;reflexivity. Qed.

Definition swu_literal_candidate_values t :=
  let s:=t*t in let a:=s*swu_negc_constant in let w:=s+8 in let b:=s*3 in
  let i:=swu_inv (w*b) in (a*(b*i)+swu_d_constant,w*w*w*(-i)+1).

(** Follow syntax before applying a word lemma. Blind unification of a leaf
    against every operation expands the 256-bit decoding tree needlessly. *)
Local Ltac swu_match_word := lazymatch goal with
| |-eqm feP ?z ?z=>apply eqm_refl
| |-eqm feP (@toZ (WordToZ 8) (@literal_fe_add Alg.CoreFunSem (?x,?y))) _=>
    apply swu_literal_add_match;swu_match_word
| |-eqm feP (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem (?x,?y))) _=>
    apply swu_literal_multiply_match;swu_match_word
| |-eqm feP (@toZ (WordToZ 8) (@literal_fe_square Alg.CoreFunSem ?x)) _=>
    apply swu_literal_square_match;swu_match_word
| |-eqm feP (@toZ (WordToZ 8) (@literal_fe_cube Alg.CoreFunSem ?x)) _=>
    apply swu_literal_cube_match;swu_match_word
| |-eqm feP (@toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem ?x)) _=>
    apply swu_literal_negate_match;swu_match_word
| |-eqm feP (@toZ (WordToZ 8) (@literal_fe_invert Alg.CoreFunSem ?x)) _=>
    apply swu_literal_inverse_match;swu_match_word
| |-eqm feP (@toZ (WordToZ 8) (@fromZ (WordToZ 8) ?z)) _=>
    apply swu_fromZ_match;unfold swu_negc_constant,swu_d_constant;lia
| |-eqm feP (@toZ (WordToZ 8) (@literal_fe_one256 Alg.CoreFunSem tt)) 1=>exact swu_one_match
end.

Lemma swu_literal_candidates_match (t:Ty.tySem (Word 8)) :
  let '(x1,x3):=@literal_swu_candidates Alg.CoreFunSem t in
  eqm feP (@toZ (WordToZ 8) x1) (fst (swu_literal_candidate_values (@toZ (WordToZ 8) t))) /\
  eqm feP (@toZ (WordToZ 8) x3) (snd (swu_literal_candidate_values (@toZ (WordToZ 8) t))).
Proof.
  rewrite literal_swu_candidates_step;cbn zeta;cbn [fst snd].
  unfold swu_literal_candidate_values;cbn [fst snd].
  rewrite swu_spec_negc_value,swu_spec_d_value;split;swu_match_word.
Qed.
Local Existing Instance eqm_setoid.
Local Existing Instance Zplus_eqm.
Local Existing Instance Zmult_eqm.
Local Existing Instance Zopp_eqm.
Lemma swu_literal_values_c t :
  eqm feP (fst (swu_literal_candidate_values t)) (swu_c_candidate1 t) /\
  eqm feP (snd (swu_literal_candidate_values t)) (swu_c_candidate3 t).
Proof.
  unfold swu_literal_candidate_values;cbn [fst snd].
  replace (t*t*3) with (3*t*t) by ring.
  change (eqm feP (t*t*swu_negc_constant*(3*t*t*swu_inv ((t*t+8)*(3*t*t)))+swu_d_constant)
    (swu_c_candidate1 t) /\
    eqm feP ((t*t+8)*(t*t+8)*(t*t+8)*(-swu_inv ((t*t+8)*(3*t*t)))+1) (swu_c_candidate3 t)).
  setoid_rewrite (swu_joint_inverse_opposite t).
  split;unfold swu_c_candidate1,swu_c_candidate3;unfold eqm;f_equal;ring.
Qed.
Lemma swu_literal_candidates_c (t:Ty.tySem (Word 8)) :
  let '(x1,x3):=@literal_swu_candidates Alg.CoreFunSem t in
  eqm feP (@toZ (WordToZ 8) x1) (swu_c_candidate1 (@toZ (WordToZ 8) t)) /\
  eqm feP (@toZ (WordToZ 8) x3) (swu_c_candidate3 (@toZ (WordToZ 8) t)).
Proof.
  pose proof (swu_literal_candidates_match t) as Match.
  pose proof (swu_literal_values_c (@toZ (WordToZ 8) t)) as Values.
  destruct (@literal_swu_candidates Alg.CoreFunSem t) as [x1 x3].
  destruct Match as [M1 M3];destruct Values as [V1 V3];split;
    [exact (eqm_trans feP _ _ _ M1 V1)|exact (eqm_trans feP _ _ _ M3 V3)].
Qed.

Definition swu_radicand (x:Ty.tySem (Word 8)) :=
  @literal_fe_add Alg.CoreFunSem (curve_seven_word,@literal_fe_cube Alg.CoreFunSem x).
Lemma swu_radicand_match x a : eqm feP (@toZ (WordToZ 8) x) a ->
  eqm feP (@toZ (WordToZ 8) (swu_radicand x)) (swu_cubic a).
Proof.
  intro X;unfold swu_radicand,swu_cubic;replace (a^3+7) with (7+a*a*a) by ring.
  apply swu_literal_add_match;
    [unfold eqm;rewrite curve_seven_value;reflexivity|apply swu_literal_cube_match;exact X].
Qed.
Lemma swu_second_candidate_match x t :
  eqm feP (@toZ (WordToZ 8) x) (swu_c_candidate1 t) ->
  eqm feP (@toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem
    (@literal_fe_add Alg.CoreFunSem (x,@literal_fe_one256 Alg.CoreFunSem tt)))) (swu_c_candidate2 t).
Proof.
  intro X;unfold swu_c_candidate2;apply swu_literal_negate_match;apply swu_literal_add_match;
    [exact X|exact swu_one_match].
Qed.
Lemma swu_literal_third_check (t:Ty.tySem (Word 8)) :
  let '(x1,x3):=@literal_swu_candidates Alg.CoreFunSem t in
  let x2:=@literal_fe_negate Alg.CoreFunSem
    (@literal_fe_add Alg.CoreFunSem (x1,@literal_fe_one256 Alg.CoreFunSem tt)) in
  Bit.toBool (literal_root_check (swu_radicand x1))=Datatypes.false ->
  Bit.toBool (literal_root_check (swu_radicand x2))=Datatypes.false ->
  Bit.toBool (literal_root_check (swu_radicand x3))=Datatypes.true.
Proof.
  pose proof (swu_literal_candidates_c t) as Match.
  destruct (@literal_swu_candidates Alg.CoreFunSem t) as [x1 x3].
  destruct Match as [M1 M3];cbn zeta;intros F1 F2.
  eapply (swu_c_candidates_third (swu_radicand x1)
    (swu_radicand (@literal_fe_negate Alg.CoreFunSem
      (@literal_fe_add Alg.CoreFunSem (x1,@literal_fe_one256 Alg.CoreFunSem tt))))
    (swu_radicand x3) (@toZ (WordToZ 8) t)).
  - apply swu_radicand_match;exact M1.
  - apply swu_radicand_match;apply swu_second_candidate_match;exact M1.
  - apply swu_radicand_match;exact M3.
  - exact F1.
  - exact F2.
Qed.

Local Transparent literal_root_check.
Lemma swu_y_from_x_check (x:Ty.tySem (Word 8)) :
  @literal_y_from_x Alg.CoreFunSem x=
  if Bit.toBool (literal_root_check (swu_radicand x))
    then inr (literal_root_candidate (swu_radicand x)) else inl tt.
Proof.
  rewrite literal_y_from_x_step;fold (swu_radicand x);rewrite literal_root_result_step.
  fold (literal_root_check (swu_radicand x)).
  destruct (literal_root_check (swu_radicand x)) as [u|u];destruct u;reflexivity.
Qed.
Local Opaque literal_root_check.
Definition swu_selected_candidate (t:Ty.tySem (Word 8)) :=
  let '(x1,x3):=@literal_swu_candidates Alg.CoreFunSem t in
  let x2:=@literal_fe_negate Alg.CoreFunSem
    (@literal_fe_add Alg.CoreFunSem (x1,@literal_fe_one256 Alg.CoreFunSem tt)) in
  if Bit.toBool (literal_root_check (swu_radicand x1))
    then (x1,literal_root_candidate (swu_radicand x1))
  else if Bit.toBool (literal_root_check (swu_radicand x2))
    then (x2,literal_root_candidate (swu_radicand x2))
  else (x3,literal_root_candidate (swu_radicand x3)).
Lemma swu_select_branch_views (x1 x2 x3 y1 y2 y3:Ty.tySem (Word 8)) (f1 f2 f3:bool) :
  (f1=Datatypes.false -> f2=Datatypes.false -> f3=Datatypes.true) ->
  (match (if f1 then inr y1 else inl tt) with
   | inr y=>(x1,y)
   | inl _=>match (if f2 then inr y2 else inl tt) with
     | inr y=>(x2,y)
     | inl _=>match (if f3 then inr y3 else inl tt) with
       | inr y=>(x3,y)
       | inl _=>(@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt)
       end
     end
   end)=(if f1 then (x1,y1) else if f2 then (x2,y2) else (x3,y3)).
Proof.
  intro Third;destruct f1,f2;try reflexivity;rewrite (Third eq_refl eq_refl);reflexivity.
Qed.
Lemma swu_literal_select_no_fallback t :
  @literal_swu_select Alg.CoreFunSem (@literal_swu_candidates Alg.CoreFunSem t)=swu_selected_candidate t.
Proof.
  pose proof (swu_literal_third_check t) as Third;unfold swu_selected_candidate.
  destruct (@literal_swu_candidates Alg.CoreFunSem t) as [x1 x3].
  rewrite literal_swu_select_step;cbn zeta in *;rewrite !swu_y_from_x_check.
  apply swu_select_branch_views;exact Third.
Qed.
Lemma swu_literal_selected_step t : @literal_swu Alg.CoreFunSem t=
  if Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem t)
    then @literal_ge_negate Alg.CoreFunSem (swu_selected_candidate t) else swu_selected_candidate t.
Proof. rewrite literal_swu_step,swu_literal_select_no_fallback;reflexivity. Qed.
