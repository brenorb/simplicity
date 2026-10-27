(** Numeric meaning of the literal signed-half projections and extension.
    These bridges retain the original Core terms used by split_lambda. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_toZ C.jet_predicate_spec C.jet_subtract_spec C.jet_canonical_add_adapter
 C.jet_secp_canonical_scalar C.jet_secp_split_literal C.jet_secp_wnaf_literal_signed C.jet_secp_wnaf5_input.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition split_half_signed (p:Ty.tySem literal_split_half) := literal_wnaf_signed_value (fst p) (snd p).

Lemma split_half_residue (p:Ty.tySem literal_split_half) :
 wnaf5_input_scalar (fst p) (snd p)=split_half_signed p mod canonical_group_order.
Proof.
 destruct p as [sg w];pose proof (word_value_bounds 7 w) as W.
 change (0<= @toZ (WordToZ 7) w<2^128) in W.
 assert (N:2^128<canonical_group_order) by (unfold canonical_group_order;lia).
 destruct sg as [u|u];destruct u.
 - change (@toZ (WordToZ 7) w=(@toZ (WordToZ 7) w-2^128*0) mod canonical_group_order).
   replace (@toZ (WordToZ 7) w-2^128*0) with (@toZ (WordToZ 7) w) by ring.
   symmetry;apply Z.mod_small;lia.
 - change (canonical_group_order-(2^128- @toZ (WordToZ 7) w)=
    (@toZ (WordToZ 7) w-2^128*1) mod canonical_group_order).
   apply Z.mod_unique with (q:= -1);[left;lia|ring].
Qed.


Lemma split_half_of_balance (sg:Ty.tySem Bit) (hi lo:Ty.tySem (Word 7)) delta :
 -2^128<delta<2^128 ->
 @toZ (WordToZ 7) hi*2^128+ @toZ (WordToZ 7) lo-2^256* @toZ BitToZ sg=delta ->
 split_half_signed (sg,lo)=delta.
Proof.
 intros Small Balance.
 pose proof (word_value_bounds 7 hi) as Hi;pose proof (word_value_bounds 7 lo) as Lo.
 change (0<= @toZ (WordToZ 7) hi<2^128) in Hi.
 change (0<= @toZ (WordToZ 7) lo<2^128) in Lo.
 destruct sg as [u|u];destruct u.
 - change (@toZ BitToZ (inl tt)) with 0 in Balance.
   change (@toZ (WordToZ 7) lo-2^128*0=delta);lia.
 - change (@toZ BitToZ (inr tt)) with 1 in Balance.
   change (@toZ (WordToZ 7) lo-2^128*1=delta);lia.
Qed.
Lemma split_word_value (p:Ty.tySem (Word 8)) :
 @toZ (WordToZ 8) p= @toZ (WordToZ 7) (fst p)*2^128+ @toZ (WordToZ 7) (snd p).
Proof. destruct p;reflexivity. Qed.
Local Opaque subtract_word_spec.
Lemma split_subtract_half_numeric (a b:Ty.tySem (Word 8)) :
 -2^128< @toZ (WordToZ 8) a- @toZ (WordToZ 8) b<2^128 ->
 let p:=@subtract_word_spec Alg.CoreFunSem 8 (a,b) in
 split_half_signed (fst p,snd (snd p))= @toZ (WordToZ 8) a- @toZ (WordToZ 8) b.
Proof.
 intro Small;cbv zeta.
 apply split_half_of_balance with
  (hi:=fst (snd (@subtract_word_spec Alg.CoreFunSem 8 (a,b))));[exact Small|].
 pose proof (subtract_word_spec_numeric 8 a b) as Balance.
 change (@toZ (WordToZ 8) (snd (@subtract_word_spec Alg.CoreFunSem 8 (a,b)))-
  2^256* @toZ BitToZ (fst (@subtract_word_spec Alg.CoreFunSem 8 (a,b)))=
  @toZ (WordToZ 8) a- @toZ (WordToZ 8) b) in Balance.
 rewrite split_word_value in Balance;exact Balance.
Qed.
Lemma split_carry_mod c x : 0<=x<2^256 -> x=(c*2^256+x) mod 2^256.
Proof. intro X;apply Z.mod_unique with (q:=c);[left;exact X|ring]. Qed.
Lemma split_add_payload (a b:Ty.tySem (Word 8)) :
 @toZ (WordToZ 8) (snd (@canonical_add_word 8 Alg.CoreFunSem (a,b)))=
 (@toZ (WordToZ 8) a+ @toZ (WordToZ 8) b) mod 2^256.
Proof.
 rewrite canonical_add_word_matches_adder.
 pose proof (Word.adder_correct 8 a b) as Sum.
 assert (Expand:forall p:Ty.tySem (Ty.Prod Bit (Word 8)),
  @toZ (PairToZ BitToZ (WordToZ 8)) p=
  @toZ BitToZ (fst p)*2^256+ @toZ (WordToZ 8) (snd p)) by (intros [c w];reflexivity).
 rewrite Expand in Sum;rewrite <-Sum.
 set (result:=@Word.adder 8 Alg.CoreFunSem (a,b)).
 change (@toZ (WordToZ 8) (snd result)=
  (@toZ BitToZ (fst result)*2^256+ @toZ (WordToZ 8) (snd result)) mod 2^256).
 apply split_carry_mod;apply word_value_bounds.
Qed.

Lemma literal_split_high_value : @toZ (WordToZ 7) (@literal_split_high Alg.CoreFunSem tt)=2^128-1.
Proof. vm_compute;reflexivity. Qed.

Local Opaque canonical_add_word Alg.scribe literal_split_high Word.zero.
Lemma literal_split_signed_scalar_numeric (p:Ty.tySem literal_split_half) :
 @toZ (WordToZ 8) (@literal_split_signed_scalar Alg.CoreFunSem p)=wnaf5_input_scalar (fst p) (snd p).
Proof.
 destruct p as [sg w];pose proof (word_value_bounds 7 w) as W.
 change (0<= @toZ (WordToZ 7) w<2^128) in W.
 assert (N:2^128<canonical_group_order<2^256) by (unfold canonical_group_order;lia).
 destruct sg as [u|u];destruct u.
 - change (@toZ (WordToZ 7) (@Word.zero 7 Alg.CoreFunSem tt)*2^128+ @toZ (WordToZ 7) w=
    @toZ (WordToZ 7) w).
   rewrite Word.zero_correct;ring.
 - change (@toZ (WordToZ 8) (snd (@canonical_add_word 8 Alg.CoreFunSem
    ((@literal_split_high Alg.CoreFunSem tt,w),@Alg.scribe Ty.Unit (Word 8) canonical_group_word Alg.CoreFunSem tt)))=
    canonical_group_order-(2^128- @toZ (WordToZ 7) w)).
   rewrite Alg.scribe_correct,split_add_payload,canonical_group_word_value.
   change ((@toZ (WordToZ 7) (@literal_split_high Alg.CoreFunSem tt)*2^128+
    @toZ (WordToZ 7) w+canonical_group_order) mod 2^256=
    canonical_group_order-(2^128- @toZ (WordToZ 7) w)).
   rewrite literal_split_high_value.
   replace ((2^128-1)*2^128+ @toZ (WordToZ 7) w+canonical_group_order) with
    ((canonical_group_order-(2^128- @toZ (WordToZ 7) w))+1*2^256) by ring.
   rewrite Z.mod_add by lia;apply Z.mod_small;lia.
Qed.
