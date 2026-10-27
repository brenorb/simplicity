(** Faithful structural port of lookupTable5 and its pos/neg branches from
    Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:785--791. The signed
    nibble denotes the odd digit 2*signed4+1, as in the fixed wNAF program. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_scalar_table_literal C.jet_secp_gej_negate_literal
 C.jet_secp_globalz_pass2 C.jet_secp_globalz_word_walk C.jet_secp_wnaf5_literal_next
 C.jet_secp_table_get_control C.jet_secp_rescale_literal.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_lookup5_branch_type :=
 Ty.Prod Bit (Ty.Prod (Word 1) (literal_table_vector 3)).
Definition literal_lookup5_pos {term:Alg.Core.Algebra} : term literal_lookup5_branch_type literal_table_ge :=
 (I O I H &&& (I O O H &&& ((O H &&& I I H) >>> Bit.cond (I H) (O H))
  >>> Bit.cond (I H) (O H))) >>> Bit.cond (I H) (O H).
Definition literal_lookup5_neg {term:Alg.Core.Algebra} : term literal_lookup5_branch_type literal_table_ge :=
 (I O I H &&& (I O O H &&& ((O H &&& I I H) >>> Bit.cond (O H) (I H))
  >>> Bit.cond (O H) (I H))) >>> Bit.cond (O (@literal_ge_negate term)) (I (@literal_ge_negate term)).
Definition literal_lookup5 {term:Alg.Core.Algebra} :
 term (Ty.Prod (Word 2) (literal_table_vector 3)) literal_table_ge :=
 (O O O H &&& O O I H &&& O I H &&& I H) >>>
 Bit.cond (@literal_lookup5_neg term) (@literal_lookup5_pos term).

Local Open Scope Z_scope.
Definition lookup5_digit nib := 2*literal_wnaf_signed4 nib+1.
Definition lookup5_negative (nib:Ty.tySem (Word 2)) := Bit.toBool (fst (fst nib)).
Definition lookup5_index nib := (Z.abs (lookup5_digit nib)-1)/2.
Local Opaque literal_ge_negate rescale_field_output.
Local Ltac lookup5_cases nib :=
 destruct nib as [[b3 b2] [b1 b0]];
 destruct b3 as [u3|u3];destruct u3;destruct b2 as [u2|u2];destruct u2;
 destruct b1 as [u1|u1];destruct u1;destruct b0 as [u0|u0];destruct u0.

Lemma lookup5_index_range nib : 0<=lookup5_index nib<8.
Proof.
 lookup5_cases nib;vm_compute;split;congruence.
Qed.
Lemma lookup5_digit_source nib : lookup5_digit nib=table_get_digit (lookup5_negative nib) (lookup5_index nib).
Proof.
 lookup5_cases nib;reflexivity.
Qed.

Theorem literal_lookup5_decoded nib xs ys :
 @literal_lookup5 Alg.CoreFunSem (nib,globalz_word_vector (globalz_decoded_points xs ys))=
 let p:=globalz_decoded_points xs ys (Z.to_nat (lookup5_index nib)) in
 if lookup5_negative nib then @literal_ge_negate Alg.CoreFunSem p else p.
Proof.
 lookup5_cases nib;reflexivity.
Qed.
