(** Reuse the checked add_64 bridge for the canonical totalFee fold. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Util.Option.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit Simplicity.Digest.
Require Import C.jet_elements_prim C.jet_elements_total_fee_literal C.jet_elements_fee_literal
 C.jet_add64_wide_word C.jet_wide_spec C.jet_wide C.jet_word_repr C.jet_equality_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque Word.adder fee_script_hash_test equality_spec.
Definition fee_int64_word(v:int64):Ty.tySem Word64:=@fromZ(WordToZ 6)(Int64.unsigned v).
Lemma fee_int64_word_toZ v:toZ(fee_int64_word v)=Int64.unsigned v.
Proof.
 unfold fee_int64_word;rewrite to_fromZ.
 change(two_power_nat(bitSize(WordToZ 6)))with Int64.modulus.
 apply Z.mod_small;apply Int64.unsigned_range.
Qed.
Lemma fee_literal_add64 v a:
 snd(@Word.adder 6 Alg.CoreFunSem(fee_int64_word v,fee_int64_word a))=fee_int64_word(Int64.add a v).
Proof.
 pose proof(add64_values_denote_input v a (fee_int64_word v)(fee_int64_word a)
  (eq_sym(fee_int64_word_toZ v))(eq_sym(fee_int64_word_toZ a)))as Add.
 apply(f_equal(@snd (Ty.tySem Bit)(Ty.tySem Word64)))in Add.
 cbn [snd]in Add.
 unfold add64_spec_value,add64_spec in Add.
 rewrite Int64.zero_ext_above in Add by(change Int64.zwordsize with 64;lia).
 change(fee_int64_word(Int64.add v a)=snd(@Word.adder 6 Alg.CoreFunSem(fee_int64_word v,fee_int64_word a)))in Add.
 rewrite Int64.add_commut;exact(eq_sym Add).
Qed.

Definition fee_literal_amount(key:Ty.tySem Word256)(o:txOutput):int64:=
 match txoAsset o,txoAmount o with
 |Explicit asset,Explicit v=>
  if andb(Bit.toBool(fee_script_hash_test o))
   (Bit.toBool(@equality_spec Word256 Alg.CoreFunSem(key,from_hash256 asset)))
  then v else Int64.zero
 |_,_=>Int64.zero end.
Lemma fee_literal_zero_int64:total_fee_literal_zero=fee_int64_word Int64.zero.
Proof. unfold total_fee_literal_zero,fee_int64_word;reflexivity. Qed.
Local Opaque fee_int64_word from_hash256.
Lemma fee_literal_step_int64 key a o:
 total_fee_literal_step key(fee_int64_word a)o=
 fee_int64_word(Int64.add a(fee_literal_amount key o)).
Proof.
 unfold total_fee_literal_step,fee_literal_amount.
 destruct(txoAsset o)as [h | p pr];destruct(txoAmount o)as [v | q qr];
 try solve[rewrite Int64.add_zero;reflexivity].
 destruct(Bit.toBool(fee_script_hash_test o));
 destruct(Bit.toBool(@equality_spec Word256 Alg.CoreFunSem(key,from_hash256 h)));cbn [andb];
 first[apply fee_literal_add64|rewrite Int64.add_zero;reflexivity].
Qed.
Lemma fee_literal_fold_int64 key outputs a:
 fold_left(total_fee_literal_step key)outputs(fee_int64_word a)=
 fee_int64_word(fold_left(fun total o=>Int64.add total(fee_literal_amount key o))outputs a).
Proof.
 revert a;induction outputs as [|o outputs IH];intro a;[reflexivity|].
 cbn [fold_left];rewrite fee_literal_step_int64;apply IH.
Qed.
Definition fee_literal_sum(key:Ty.tySem Word256)(environment:Elements.env):int64:=
 fold_left(fun total o=>Int64.add total(fee_literal_amount key o))
 (sigTxOut(Elements.envTx environment))Int64.zero.
Theorem total_fee_literal_result_int64 key environment:
 total_fee_literal_result key environment=fee_int64_word(fee_literal_sum key environment).
Proof.
 unfold total_fee_literal_result,fee_literal_sum.
 rewrite fee_literal_zero_int64;apply fee_literal_fold_int64.
Qed.
Theorem elements_total_fee_uint64_sem key environment:
 @elements_total_fee_spec(PrimitivePrimSem option_Monad_Zero)key environment=
 Some(fee_int64_word(fee_literal_sum key environment)).
Proof. rewrite elements_total_fee_sem,total_fee_literal_result_int64;reflexivity. Qed.
