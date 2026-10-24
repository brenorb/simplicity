(** Exact serialized value of the point selected by the four C moves.
    Canonicality is proved for the literal program's outputs, not assumed
    of the C limbs. No raw-p zero corner is silently identified with 0. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_multiply_finish_product
  C.jet_secp_multiply_normalize_bridge C.jet_secp_rescale_literal C.jet_secp_root_chain_numeric
  C.jet_secp_swu_literal C.jet_secp_swu_literal_bridge C.jet_secp_swu_select_exec
  C.jet_secp_root_check C.jet_secp_root_literal C.jet_secp_negate_literal_contract
  C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric C.jet_secp_curve_literal
  C.jet_secp_canonical_normalize.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_swu_candidates literal_fe_add literal_fe_negate literal_fe_one256
  literal_root_candidate literal_root_check rescale_field_output.

Lemma swu_literal_add_canonical x y :
  @toZ (WordToZ 8) (@literal_fe_add Alg.CoreFunSem (x,y)) mod feP=
  @toZ (WordToZ 8) (@literal_fe_add Alg.CoreFunSem (x,y)).
Proof.
  rewrite !literal_fe_add_numeric,canonical_field_order_matches_limb_model;
    apply Z.mod_mod;unfold feP,feR;lia.
Qed.
Lemma swu_literal_negate_canonical x :
  @toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem x) mod feP=
  @toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem x).
Proof. rewrite !literal_curve_negate_numeric;apply Z.mod_mod;unfold feP,feR;lia. Qed.
Lemma swu_literal_candidates_canonical t :
  let '(x1,x3):=@literal_swu_candidates Alg.CoreFunSem t in
  @toZ (WordToZ 8) x1 mod feP=@toZ (WordToZ 8) x1 /\
  @toZ (WordToZ 8) x3 mod feP=@toZ (WordToZ 8) x3.
Proof. rewrite literal_swu_candidates_step;split;apply swu_literal_add_canonical. Qed.
Lemma swu_field_output_matches w x : root_words_match w x ->
  @toZ (WordToZ 8) x mod feP=@toZ (WordToZ 8) x -> rescale_field_output w=x.
Proof.
  intros [_ Match] Canonical;apply (toZ_injective (WordToZ 8)).
  rewrite rescale_field_output_value,field_prime_matches_normalizer,Match;exact Canonical.
Qed.
Lemma swu_selected_property (P:(nat->int64)->Prop) alpha beta a b c :
  P a -> P b -> P c -> P (swu_selected_words alpha beta a b c).
Proof. intros;destruct alpha,beta;assumption. Qed.

Theorem swu_selected_matches_literal t alpha beta x1 x2 x3 y1 y2 y3 :
  let '(a,c):=@literal_swu_candidates Alg.CoreFunSem t in
  let b:=@literal_fe_negate Alg.CoreFunSem (@literal_fe_add Alg.CoreFunSem (a,@literal_fe_one256 Alg.CoreFunSem tt)) in
  root_words_match x1 a -> root_words_match x2 b -> root_words_match x3 c ->
  rescale_field_output y1=literal_root_candidate (swu_radicand a) ->
  rescale_field_output y2=literal_root_candidate (swu_radicand b) ->
  rescale_field_output y3=literal_root_candidate (swu_radicand c) ->
  alpha=Bit.toBool (literal_root_check (swu_radicand a)) ->
  beta=Bit.toBool (literal_root_check (swu_radicand b)) ->
  (rescale_field_output (swu_selected_words alpha beta x1 x2 x3),
   rescale_field_output (swu_selected_words alpha beta y1 y2 y3))=swu_selected_candidate t.
Proof.
  pose proof (swu_literal_candidates_canonical t) as Canonical;unfold swu_selected_candidate.
  destruct (@literal_swu_candidates Alg.CoreFunSem t) as [a c];cbn zeta.
  intros MX1 MX2 MX3 Y1 Y2 Y3 A B;destruct Canonical as [C1 C3].
  pose proof (swu_field_output_matches _ _ MX1 C1) as X1.
  pose proof (swu_field_output_matches _ _ MX2 (swu_literal_negate_canonical _)) as X2.
  pose proof (swu_field_output_matches _ _ MX3 C3) as X3.
  rewrite <-A,<-B;unfold swu_selected_words;destruct alpha,beta;
    rewrite ?X1,?X2,?X3,?Y1,?Y2,?Y3;reflexivity.
Qed.
