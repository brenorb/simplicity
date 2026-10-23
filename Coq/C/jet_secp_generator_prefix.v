(** Shared exact binary prefixes. Each node computes one double and shares it
    between the zero- and one-bit continuations, preserving their exact Z. *)
From Coq Require Import ZArith List Lia.
Require Import C.jet_secp_generate_numeric.
Require Import C.jet_secp_generator_bits.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint generator_path_index (bits : list bool) : nat :=
 match bits with
 | [] => 0%nat
 | bit::tail => ((if bit then Nat.pow 2 (length tail) else 0)+generator_path_index tail)%nat
 end.
Definition generator_odd_leaf base a := literal_norm_fast (literal_generate_bit base a true).
Fixpoint generator_prefix_values depth base a :=
 match depth with
 | Datatypes.O => [generator_odd_leaf base a]
 | Datatypes.S k =>
     let doubled:=literal_double_eval a in
     generator_prefix_values k base doubled ++
       generator_prefix_values k base (literal_mixed_eval doubled base)
 end.

Lemma generator_path_index_bound bits : (generator_path_index bits<Nat.pow 2 (length bits))%nat.
Proof.
 induction bits as [|bit tail IH];[cbn [generator_path_index length Nat.pow];lia|].
 cbn [generator_path_index length Nat.pow];destruct bit;lia.
Qed.
Lemma generator_prefix_values_length depth base a :
 length (generator_prefix_values depth base a)=Nat.pow 2 depth.
Proof.
 revert a;induction depth as [|depth IH];intro a;[reflexivity|].
 cbn [generator_prefix_values];rewrite app_length,!IH;cbn [Nat.pow];lia.
Qed.

Theorem generator_prefix_values_lookup depth base a bits default : length bits=depth ->
 nth (generator_path_index bits) (generator_prefix_values depth base a) default=
 generator_odd_leaf base (fold_left (literal_generate_bit base) bits a).
Proof.
 revert a bits;induction depth as [|depth IH];intros a bits Length.
 - destruct bits;[reflexivity|discriminate].
 - destruct bits as [|bit tail];[discriminate|].
   cbn [length] in Length;injection Length as TailLength.
   cbn [generator_path_index generator_prefix_values fold_left];destruct bit.
   + rewrite app_nth2 by (rewrite generator_prefix_values_length,<-TailLength;pose proof (generator_path_index_bound tail);lia).
     rewrite generator_prefix_values_length,<-TailLength.
     replace ((Nat.pow 2 (length tail)+generator_path_index tail)-Nat.pow 2 (length tail))%nat
       with (generator_path_index tail) by lia.
     rewrite TailLength;apply IH;exact TailLength.
   + rewrite app_nth1 by (rewrite generator_prefix_values_length,<-TailLength;apply generator_path_index_bound).
     apply IH;exact TailLength.
Qed.

Lemma generator_path_index_value bits : Z.of_nat (generator_path_index bits)=generator_bits_value bits.
Proof.
 induction bits as [|bit tail IH];[reflexivity|].
 cbn [generator_path_index generator_bits_value];destruct bit;cbn [Nat.add].
 - rewrite Nat2Z.inj_add,Nat2Z.inj_pow,IH;change (Z.of_nat 2) with 2;ring.
 - rewrite Z.mul_0_l,Z.add_0_l;exact IH.
Qed.
