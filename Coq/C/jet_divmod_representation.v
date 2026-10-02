(** Recover the complete canonical quotient/remainder pair from the already
    checked projection bridges; this is not a replacement specification. *)
From Coq Require Import ZArith.
Require Import Simplicity.Word C.jet_division_core_spec C.jet_division_value.
Require Import C.jet_division_result_spec.
Set Default Timeout 10.

Lemma div_mod_word_representation n (x y : Ty.tySem (Word n)) :
  (@fromZ (WordToZ n) (division_numeric Datatypes.false (@toZ (WordToZ n) x) (@toZ (WordToZ n) y)),
   @fromZ (WordToZ n) (division_numeric Datatypes.true (@toZ (WordToZ n) x) (@toZ (WordToZ n) y))) =
  @div_mod_word_spec n Alg.CoreFunSem (x,y).
Proof.
  rewrite !division_word_representation.
  change ((fst (@div_mod_word_spec n Alg.CoreFunSem (x,y)),
    snd (@div_mod_word_spec n Alg.CoreFunSem (x,y))) = @div_mod_word_spec n Alg.CoreFunSem (x,y)).
  symmetry. apply surjective_pairing.
Qed.
