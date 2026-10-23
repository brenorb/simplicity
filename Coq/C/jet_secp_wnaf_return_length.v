(** The original C return length removes only leading zero digits from the
    already-proved high-to-low literal vector. *)
From Coq Require Import ZArith Lia List.
Require Import C.jet_secp_wnaf_loop C.jet_secp_wnaf_literal_array.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit C.jet_secp_wnaf_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma wnaf_above_last_zero digits bit last : wnaf_last digits bit last ->
 forall i,last<i -> 0<=i<bit -> digits i=0.
Proof.
 intros (_ & Highest & _) i Above Range;destruct (Z.eq_dec (digits i) 0);[assumption|].
 pose proof (Highest i Range n);lia.
Qed.

Theorem wnaf_return_length_slice count digits last :
 wnaf_last digits (Z.of_nat count) last ->
 rev (wnaf_slice count digits 0)=
 repeat 0 (count-Z.to_nat (last+1))++rev (wnaf_slice (Z.to_nat (last+1)) digits 0).
Proof.
 intro Last;pose proof Last as (Bound & Highest & Present).
 assert (Length : (Z.to_nat (last+1)<=count)%nat)
   by (apply Nat2Z.inj_le;rewrite Z2Nat.id by lia;lia).
 replace count with (Z.to_nat (last+1)+(count-Z.to_nat (last+1)))%nat at 1 by lia.
 rewrite wnaf_slice_app,rev_app_distr.
 assert (Zeros : wnaf_slice (count-Z.to_nat (last+1)) digits (0+Z.of_nat (Z.to_nat (last+1)))=
   repeat 0 (count-Z.to_nat (last+1))).
 { apply wnaf_slice_constant;intros i Range.
   rewrite Nat2Z.inj_sub in Range by exact Length;rewrite Z2Nat.id in Range by lia.
   eapply wnaf_above_last_zero;[exact Last|lia|lia]. }
 rewrite Zeros,rev_repeat;reflexivity.
Qed.

Theorem wnaf_literal_return_length m b base digits last (word : Ty.tySem (Word 7)) :
 wnaf_array_state m b base 129 15 1 129 last digits ->
 map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word))=
   rev (map (fun i=>digits (Z.of_nat i)) (seq 0 129)) ->
 map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word))=
   repeat 0 (129-Z.to_nat (last+1))++rev (wnaf_slice (Z.to_nat (last+1)) digits 0).
Proof.
 intros Array Literal;rewrite Literal.
 replace (map (fun i=>digits (Z.of_nat i)) (seq 0 129)) with (wnaf_slice 129 digits 0).
 - apply wnaf_return_length_slice;exact (wnaf_array_last _ _ _ _ _ _ _ _ _ Array).
 - rewrite wnaf_slice_seq;apply map_ext;intro i;f_equal;lia.
Qed.
