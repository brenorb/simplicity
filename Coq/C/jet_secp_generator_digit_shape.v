(** Every valid literal wNAF15 digit has the complete-table prefix shape;
    the scalar domain is derived from its existing odd/range invariants. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_generator_bits C.jet_secp_generator_prefix
 C.jet_secp_wnaf_literal_mask.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma generator_signed_bits_shape (sign second last : bool) k n :
 0<=k<8192 ->
 n= -32768*(if sign then 1 else 0)+16384*(if second then 1 else 0)+2*k+(if last then 1 else 0) ->
 n mod 2=1 -> -16384<n<16384 ->
 second=sign /\ last=Datatypes.true /\ n=(if sign then 2*k-16383 else 2*k+1).
Proof.
 intros K Code Odd Range.
 assert (Parity : n mod 2=(if last then 1 else 0)).
 { replace n with ((if last then 1 else 0)+
     (-16384*(if sign then 1 else 0)+8192*(if second then 1 else 0)+k)*2) by (rewrite Code;ring).
   rewrite Z.mod_add by lia;destruct last;reflexivity. }
 assert (Last : last=Datatypes.true) by (destruct last;[reflexivity|rewrite Odd in Parity;discriminate]).
 subst last;destruct sign,second;repeat split;try reflexivity;lia.
Qed.

Theorem generator_wnaf_digit_decomposition (word : Ty.tySem (Word 4)) :
 literal_wnaf_signed16 word mod 2=1 -> -16384<literal_wnaf_signed16 word<16384 ->
 exists neg bits,length bits=13%nat /\ literal_generator_bits 4 word=[neg;neg]++bits++[Datatypes.true] /\
 literal_wnaf_signed16 word=(if neg then 2*Z.of_nat (generator_path_index bits)-16383
   else 2*Z.of_nat (generator_path_index bits)+1).
Proof.
 destruct word as [[[[sign second] w2] w4] [u4 [u2 [u1 last]]]].
 intros Odd Range.
 set (bits:=(literal_generator_bits 1 w2++literal_generator_bits 2 w4)++
   (literal_generator_bits 2 u4++literal_generator_bits 1 u2++[Bit.toBool u1])).
 assert (Length : length bits=13%nat).
 { unfold bits;rewrite !app_length,!literal_generator_bits_length;reflexivity. }
 assert (Bits : literal_generator_bits 4 ((((sign,second),w2),w4),(u4,(u2,(u1,last))))=
   [Bit.toBool sign;Bit.toBool second]++bits++[Bit.toBool last]).
 { unfold bits;cbn [literal_generator_bits fst snd app];reflexivity. }
 pose proof (literal_generator_bits_value 4 ((((sign,second),w2),w4),(u4,(u2,(u1,last))))) as Numeric.
 pose proof (generator_path_index_bound bits) as Bound.
 rewrite Length in Bound.
 apply Nat2Z.inj_lt in Bound;rewrite Nat2Z.inj_pow in Bound.
 change (Z.of_nat (generator_path_index bits)<8192) in Bound.
 assert (K : 0<=Z.of_nat (generator_path_index bits)<8192)
   by (pose proof (Nat2Z.is_nonneg (generator_path_index bits));lia).
 assert (Signed : literal_wnaf_signed16 ((((sign,second),w2),w4),(u4,(u2,(u1,last))))=
   @toZ (WordToZ 4) ((((sign,second),w2),w4),(u4,(u2,(u1,last))))-65536*@toZ BitToZ sign)
   by reflexivity.
 clearbody bits.
 rewrite Bits in Numeric.
 rewrite !generator_bits_value_app,!app_length,Length in Numeric.
 cbn [generator_bits_value length] in Numeric.
 rewrite <-generator_path_index_value in Numeric.
 assert (Code : literal_wnaf_signed16 ((((sign,second),w2),w4),(u4,(u2,(u1,last))))=
   -32768*(if Bit.toBool sign then 1 else 0)+16384*(if Bit.toBool second then 1 else 0)+
   2*Z.of_nat (generator_path_index bits)+(if Bit.toBool last then 1 else 0)).
 { rewrite Signed,<-Numeric.
   assert (SignValue : @toZ BitToZ sign=(if Bit.toBool sign then 1 else 0))
     by (destruct sign as [s|s];destruct s;reflexivity).
   rewrite SignValue.
   change (2^Z.of_nat 1) with 2;change (2^Z.of_nat 0) with 1;
     change (2^Z.of_nat (13+1)) with 16384;ring. }
 destruct (generator_signed_bits_shape (Bit.toBool sign) (Bit.toBool second) (Bit.toBool last)
   _ _ K Code Odd Range) as (Second & Last & Value).
 exists (Bit.toBool sign),bits;split.
 - exact Length.
 - split.
   + etransitivity;[exact Bits|].
     rewrite Second,Last;reflexivity.
   + exact Value.
Qed.
