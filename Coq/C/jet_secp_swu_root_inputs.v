(** Connect the derived loose C radicands to the exact literal Simplicity
    root inputs. Input equality is modular, so no canonical-limb premise
    is introduced for the original reader or any intermediate candidate. *)
From Coq Require Import ZArith Znumtheory Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.modinv C.jet_toZ C.jet_secp_fe_math C.jet_secp_swu_candidates
  C.jet_secp_swu_literal C.jet_secp_swu_literal_bridge C.jet_secp_root_chain_numeric
  C.jet_secp_square_columns C.jet_secp_multiply_finish_product
  C.jet_secp_negate_literal_contract C.jet_secp_literal_add_program.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_swu_candidates literal_fe_negate literal_fe_add literal_fe_one256.

Lemma swu_joint_inverse_eqm t u : eqm feP t u -> swu_joint_inverse t=swu_joint_inverse u.
Proof.
  intro E;unfold swu_joint_inverse,swu_inv;apply modInv_eqm.
  apply Zmult_eqm.
  - apply Zplus_eqm;[apply Zmult_eqm;exact E|reflexivity].
  - apply Zmult_eqm;[|exact E];apply Zmult_eqm;[reflexivity|exact E].
Qed.
Lemma swu_candidate1_eqm t u : eqm feP t u -> eqm feP (swu_c_candidate1 t) (swu_c_candidate1 u).
Proof.
  intro E;unfold swu_c_candidate1;rewrite (swu_joint_inverse_eqm t u E).
  apply Zplus_eqm;[reflexivity|];apply Zmult_eqm;[|reflexivity].
  apply Zmult_eqm.
  - apply Zmult_eqm;[|exact E];apply Zmult_eqm;[reflexivity|exact E].
  - apply Zmult_eqm;[|exact E];apply Zmult_eqm;[reflexivity|exact E].
Qed.
Lemma swu_candidate2_eqm t u : eqm feP t u -> eqm feP (swu_c_candidate2 t) (swu_c_candidate2 u).
Proof.
  intro E;unfold swu_c_candidate2;apply Zopp_eqm;apply Zplus_eqm;
    [apply swu_candidate1_eqm;exact E|reflexivity].
Qed.
Lemma swu_candidate3_eqm t u : eqm feP t u -> eqm feP (swu_c_candidate3 t) (swu_c_candidate3 u).
Proof.
  intro E;unfold swu_c_candidate3;rewrite (swu_joint_inverse_eqm t u E).
  apply Zplus_eqm;[reflexivity|];apply Zmult_eqm;[|reflexivity].
  assert (S:eqm feP (t*t+8) (u*u+8)) by
    (apply Zplus_eqm;[apply Zmult_eqm;exact E|reflexivity]).
  replace ((t*t+8)^3) with ((t*t+8)*(t*t+8)*(t*t+8)) by ring.
  replace ((u*u+8)^3) with ((u*u+8)*(u*u+8)*(u*u+8)) by ring.
  apply Zmult_eqm;[apply Zmult_eqm;exact S|exact S].
Qed.

Theorem swu_root_inputs_match (t:Ty.tySem (Word 8)) w a b c :
  root_words_match w t -> square_input_bounds a -> square_input_bounds b -> square_input_bounds c ->
  eqm feP (radix_value a) (swu_cubic (swu_c_candidate1 (radix_value w))) ->
  eqm feP (radix_value b) (swu_cubic (swu_c_candidate2 (radix_value w))) ->
  eqm feP (radix_value c) (swu_cubic (swu_c_candidate3 (radix_value w))) ->
  let '(x1,x3):=@literal_swu_candidates Alg.CoreFunSem t in
  root_words_match a (swu_radicand x1) /\
  root_words_match b (swu_radicand (@literal_fe_negate Alg.CoreFunSem
    (@literal_fe_add Alg.CoreFunSem (x1,@literal_fe_one256 Alg.CoreFunSem tt)))) /\
  root_words_match c (swu_radicand x3).
Proof.
  intros [BW Input] BA BB BC VA VB VC.
  pose proof (swu_literal_candidates_c t) as Candidates.
  destruct (@literal_swu_candidates Alg.CoreFunSem t) as [x1 x3].
  destruct Candidates as [X1 X3].
  assert (A1:eqm feP (@toZ (WordToZ 8) x1) (swu_c_candidate1 (radix_value w))).
  { eapply eqm_trans;[exact X1|];apply eqm_sym;apply swu_candidate1_eqm;exact Input. }
  assert (A2:eqm feP (@toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem
    (@literal_fe_add Alg.CoreFunSem (x1,@literal_fe_one256 Alg.CoreFunSem tt))))
    (swu_c_candidate2 (radix_value w))).
  { eapply eqm_trans;[apply swu_second_candidate_match;exact X1|].
    apply eqm_sym;apply swu_candidate2_eqm;exact Input. }
  assert (A3:eqm feP (@toZ (WordToZ 8) x3) (swu_c_candidate3 (radix_value w))).
  { eapply eqm_trans;[exact X3|];apply eqm_sym;apply swu_candidate3_eqm;exact Input. }
  split;[|split];split;try assumption.
  - eapply eqm_trans;[exact VA|];apply eqm_sym;apply swu_radicand_match;exact A1.
  - eapply eqm_trans;[exact VB|];apply eqm_sym;apply swu_radicand_match;exact A2.
  - eapply eqm_trans;[exact VC|];apply eqm_sym;apply swu_radicand_match;exact A3.
Qed.
