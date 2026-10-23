(** Serial bit evaluation of the literal signed recursion. This exposes exact
    prefixes for shared finite table checking, without a group-law shortcut. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Util.Arith
 C.jet_toZ C.jet_word_repr C.jet_predicate_spec C.jet_secp_fe_math C.jet_secp_generate_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint literal_generator_bits n : Ty.tySem (Word n) -> list bool :=
 match n as k return Ty.tySem (Word k) -> list bool with
 | Datatypes.O => fun bit => [Bit.toBool bit]
 | Datatypes.S k => fun word => literal_generator_bits k (fst word) ++ literal_generator_bits k (snd word)
 end.
Definition literal_generate_bit base (a : Z*Z*Z) (bit : bool) :=
 let doubled:=literal_double_eval a in if bit then literal_mixed_eval doubled base else doubled.
Definition literal_generate_bits base (bits : list bool) :=
 match bits with
 | [] => ((0,0),0)
 | sign::tail => fold_left (literal_generate_bit base) tail
     (if sign then ((fst base mod feP,(feP-snd base) mod feP),1) else ((0,0),0))
 end.
Fixpoint generator_bits_value (bits : list bool) :=
 match bits with [] => 0 | bit::tail => (if bit then 1 else 0)*2^Z.of_nat (length tail)+generator_bits_value tail end.

Lemma literal_generator_bits_length n (word : Ty.tySem (Word n)) :
 length (literal_generator_bits n word)=Nat.pow 2 n.
Proof.
 revert word;induction n as [|n IH];intro word;[reflexivity|].
 destruct word as [hi lo];cbn [literal_generator_bits];rewrite app_length,!IH;cbn [Nat.pow];lia.
Qed.
Lemma literal_generator_bits_nonempty n (word : Ty.tySem (Word n)) : literal_generator_bits n word<>[].
Proof.
 intro Empty;pose proof (literal_generator_bits_length n word) as Size;rewrite Empty in Size.
 pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as Positive.
 cbn [length] in Size;lia.
Qed.

Lemma literal_scale_numeric_bits n base (word : Ty.tySem (Word n)) a :
 literal_scale_numeric n base word a=fold_left (literal_generate_bit base) (literal_generator_bits n word) a.
Proof.
 revert word a;induction n as [|n IH];intros word a.
 - destruct word as [u | u];destruct u;reflexivity.
 - destruct word as [hi lo];cbn [literal_scale_numeric literal_generator_bits fst snd].
   rewrite !IH,fold_left_app;reflexivity.
Qed.
Lemma literal_generate_signed_numeric_bits n base (word : Ty.tySem (Word n)) :
 literal_generate_signed_numeric n base word=literal_generate_bits base (literal_generator_bits n word).
Proof.
 revert word;induction n as [|n IH];intro word.
 - destruct word as [u | u];destruct u;reflexivity.
 - destruct word as [hi lo];cbn [literal_generate_signed_numeric literal_generator_bits fst snd].
   rewrite literal_scale_numeric_bits,IH.
   pose proof (literal_generator_bits_nonempty n hi) as Nonempty.
   destruct (literal_generator_bits n hi) as [|sign tail];[contradiction|].
   cbn [app literal_generate_bits];rewrite fold_left_app;reflexivity.
Qed.

Lemma generator_bits_value_app xs ys :
 generator_bits_value (xs++ys)=generator_bits_value xs*2^Z.of_nat (length ys)+generator_bits_value ys.
Proof.
 induction xs as [|bit xs IH];[cbn [app generator_bits_value];ring|].
 cbn [app generator_bits_value];rewrite app_length,Nat2Z.inj_add,Z.pow_add_r by lia.
 rewrite IH;ring.
Qed.
Lemma literal_generator_bits_value n (word : Ty.tySem (Word n)) :
 generator_bits_value (literal_generator_bits n word)=@toZ (WordToZ n) word.
Proof.
 revert word;induction n as [|n IH];intro word.
 - destruct word as [u | u];destruct u;reflexivity.
 - destruct word as [hi lo];cbn [literal_generator_bits fst snd].
   rewrite generator_bits_value_app,literal_generator_bits_length,!IH.
   change (@toZ (WordToZ n) hi*2^Z.of_nat (Nat.pow 2 n)+@toZ (WordToZ n) lo=
     @toZ (WordToZ n) hi*two_power_nat (ToZ.Theory.bitSize (WordToZ n))+@toZ (WordToZ n) lo).
   rewrite two_power_nat_equiv,word_bitSize;reflexivity.
Qed.
