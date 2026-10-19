(** Numeric induction for the actual Programs.Arith recursive division core.
    The smaller-call contract is discharged here, not assumed by jet consumers. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_predicate_spec C.jet_division_core_spec C.jet_division_approx_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma div2n1n_successor_unfold n (a1 a2 a3 a4 b1 b2 : Ty.tySem (Word n)) :
  @div2n1n_word_spec (S n) Alg.CoreFunSem (((a1,a2),(a3,a4)),(b1,b2)) =
  match @div2n1n_conditions (S n) Alg.CoreFunSem (((a1,a2),(a3,a4)),(b1,b2)) with
  | inl _ => @division_high_word (S (S n)) Alg.CoreFunSem tt
  | inr _ =>
    let first := @div3n2n_word_builder n Alg.CoreFunSem (@div2n1n_word_spec n Alg.CoreFunSem)
      (((a1,a2),a3),(b1,b2)) in
    let second := @div3n2n_word_builder n Alg.CoreFunSem (@div2n1n_word_spec n Alg.CoreFunSem)
      ((snd first,a4),(b1,b2)) in
    ((fst first,fst second),snd second)
  end.
Proof. reflexivity. Qed.

Lemma div2n1n_normalized_value n :
  division_normalized_result n (@div2n1n_word_spec n Alg.CoreFunSem).
Proof.
  induction n as [|n IH].
  - intros [a1 a2] b.
    destruct a1 as [[] | []], a2 as [[] | []], b as [[] | []];
      cbn; intros; try lia; split; lia.
  - intros [[a1 a2] [a3 a4]] [b1 b2] Hnorm Hbound.
    rewrite div2n1n_successor_unfold.
    assert (HG : @div2n1n_conditions (S n) Alg.CoreFunSem (((a1,a2),(a3,a4)),(b1,b2)) = Bit.one)
      by (apply div2n1n_conditions_valid; assumption).
    match goal with
    | |- context [match ?guard with inl _ => _ | inr _ => _ end] =>
      assert (HGexact : guard = (Bit.one : Ty.tySem Bit)) by exact HG;
      rewrite HGexact
    end.
    pose proof (word_modulus_positive n) as HB.
    pose proof (word_value_bounds n a4) as HA4.
    assert (Hfirst : @toZ (WordToZ (S n)) (a1,a2) * word_modulus n + @toZ (WordToZ n) a3 <
      @toZ (WordToZ (S n)) (b1,b2) * word_modulus n).
    { change (@toZ (WordToZ (S n)) (a1,a2) * word_modulus (S n) +
        (@toZ (WordToZ n) a3 * word_modulus n + @toZ (WordToZ n) a4) <
        @toZ (WordToZ (S n)) (b1,b2) * word_modulus (S n)) in Hbound.
      rewrite word_modulus_S in Hbound. nia. }
    match goal with
    | |- let qr := (let first := ?call in _) in _ => set (first := call)
    end.
    assert (HF : @toZ (WordToZ n) (fst first) * @toZ (WordToZ (S n)) (b1,b2) +
      @toZ (WordToZ (S n)) (snd first) =
        @toZ (WordToZ (S n)) (a1,a2) * word_modulus n + @toZ (WordToZ n) a3 /\
      0 <= @toZ (WordToZ (S n)) (snd first) < @toZ (WordToZ (S n)) (b1,b2)).
    { exact (div3n2n_builder_value n (@div2n1n_word_spec n Alg.CoreFunSem)
        a1 a2 a3 b1 b2 IH Hnorm Hfirst). }
    destruct first as [q1 [r1 r2]].
    destruct HF as [Hbalance1 Hrem1].
    cbn [fst snd] in Hbalance1, Hrem1.
    assert (Hsecond : @toZ (WordToZ (S n)) (r1,r2) * word_modulus n + @toZ (WordToZ n) a4 <
      @toZ (WordToZ (S n)) (b1,b2) * word_modulus n) by nia.
    cbv beta iota zeta delta [fst snd].
    match goal with
    | |- context [@div3n2n_word_builder ?m ?alg ?rec ?input] =>
      set (second := @div3n2n_word_builder m alg rec input)
    end.
    assert (HS : @toZ (WordToZ n) (fst second) * @toZ (WordToZ (S n)) (b1,b2) +
      @toZ (WordToZ (S n)) (snd second) =
        @toZ (WordToZ (S n)) (r1,r2) * word_modulus n + @toZ (WordToZ n) a4 /\
      0 <= @toZ (WordToZ (S n)) (snd second) < @toZ (WordToZ (S n)) (b1,b2)).
    { exact (div3n2n_builder_value n (@div2n1n_word_spec n Alg.CoreFunSem)
        r1 r2 a4 b1 b2 IH Hnorm Hsecond). }
    destruct second as [q2 r].
    destruct HS as [Hbalance2 Hrem2].
    cbn [fst snd] in Hbalance2, Hrem2.
    change ((@toZ (WordToZ n) q1 * word_modulus n + @toZ (WordToZ n) q2) *
      @toZ (WordToZ (S n)) (b1,b2) + @toZ (WordToZ (S n)) r =
      @toZ (WordToZ (S n)) (a1,a2) * word_modulus (S n) +
      (@toZ (WordToZ n) a3 * word_modulus n + @toZ (WordToZ n) a4) /\
      0 <= @toZ (WordToZ (S n)) r < @toZ (WordToZ (S n)) (b1,b2)).
    split; [|exact Hrem2]. rewrite word_modulus_S.
    pose proof (f_equal (fun z => z * word_modulus n) Hbalance1) as Hscaled.
    nia.
Qed.
