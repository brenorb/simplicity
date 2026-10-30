(** Literal canonical outputIsFee program and its exact option semantics.
    This does not assume that only the empty script has the empty digest. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit Simplicity.Digest.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import C.jet_elements_prim C.jet_elements_amount_jets C.jet_elements_asset_jets
 C.jet_elements_current_spec C.jet_elements_prim_sem C.jet_equality_spec C.jet_haskell_hash_word
 C.jet_haskell_word_conversion.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Set Default Timeout 10.
Module FC:=Alg.Core.Combinators.
Local Notation ConfTy a:=(Ty.Sum(Ty.Prod Bit Word256)a).
Local Notation AmountPair:=(Ty.Prod(ConfTy Word256)(ConfTy Word64)).
Definition fee_empty_hash_word:Ty.tySem Word256:=
 haskell_to_word 8(haskell_integer_hash256(hash256_to_bytelist(byteStringHash []))).
Lemma fee_empty_hash_word_matches:fee_empty_hash_word=from_hash256(byteStringHash []).
Proof. apply haskell_hash_word256. Qed.
Definition elements_fee_tail {alg:Core.Algebra}:alg((Ty.Unit+AmountPair)*Bit)(Ty.Unit+Bit):=
 case(injl unit)
 (injr((take(drop iden)&&&(take(take iden)&&&drop iden)) >>>
  case Bit.false(drop(case Bit.false(drop iden))))).
Lemma elements_fee_tail_parametric:Core.Parametric(fun alg=>@elements_fee_tail alg).
Proof.
 intros a b R;unfold elements_fee_tail.
 repeat first[apply case_Parametric|apply injl_Parametric|apply injr_Parametric|
 apply pair_Parametric|apply comp_Parametric|apply take_Parametric|apply drop_Parametric|
 apply iden_Parametric|apply unit_Parametric|apply Bit.false_Parametric].
Qed.
Definition elements_output_fee_hash_eq {alg:Primitive.Algebra}:alg Word32 Bit:=
 elements_comp
 (elements_pair(Primitive.Combinators.prim Elements.OutputScriptHash)
  (elements_core(fun core=>@Alg.scribe Word32(Ty.Unit+Word256)(inr fee_empty_hash_word)core)))
 (elements_core(fun core=>@equality_spec(Ty.Unit+Word256)core)).
Definition elements_output_fee_spec {alg:Primitive.Algebra}:alg Word32(Ty.Unit+Bit):=
 elements_comp(elements_pair(@elements_output_amount_spec alg)(@elements_output_fee_hash_eq alg))
 (elements_core(fun core=>@elements_fee_tail core)).
Definition fee_script_hash_test (o:txOutput):Bit:=
 @equality_spec(Ty.Unit+Word256)CoreFunSem
 (inr(from_hash256(byteStringHash(txoScript o))),inr fee_empty_hash_word).
Definition fee_spec_bit (o:txOutput):Bit:=
 match txoAmount o,txoAsset o with
 | Explicit _,Explicit _=>fee_script_hash_test o
 | _,_=>Bit.zero
 end.
Definition fee_spec_result (a:Ty.tySem Word32)(environment:Elements.env):Ty.tySem(Ty.Unit+Bit):=
 match nth_error(sigTxOut(Elements.envTx environment))(Z.to_nat(toZ a))with
 | Some o=>inr(fee_spec_bit o)|None=>inl tt end.
Lemma elements_fee_tail_value (asset:assetWith Datatypes.unit)(amount:amountWith Datatypes.unit)b:
 @elements_fee_tail CoreFunSem(inr(encode_asset asset,encode_amount amount),b)=
 inr(match amount,asset with Explicit _,Explicit _=>b|_,_=>Bit.zero end).
Proof.
 destruct asset as [x | [odd x] p]; destruct amount as [v | [odd' x'] p']; reflexivity.
Qed.
Lemma fee_empty_constant_parametric:
 Core.Parametric(fun core=>@Alg.scribe Word32(Ty.Unit+Word256)(inr fee_empty_hash_word)core).
Proof. intros a b R;apply Alg.scribe_Parametric. Qed.
Lemma elements_fee_hash_eq_reader a environment:
 @elements_output_fee_hash_eq(PrimitivePrimSem option_Monad_Zero)a environment=
 Some(@equality_spec(Ty.Unit+Word256)CoreFunSem
  (match nth_error(sigTxOut(Elements.envTx environment))(Z.to_nat(toZ a))with
    Some o=>inr(from_hash256(byteStringHash(txoScript o)))|None=>inl tt end,inr fee_empty_hash_word)).
Proof.
 unfold elements_output_fee_hash_eq;rewrite elements_comp_sem,elements_pair_sem.
 assert (Constant: @elements_core Word32(Ty.Unit+Word256)
 (fun core=>@Alg.scribe Word32(Ty.Unit+Word256)(inr fee_empty_hash_word)core)
 (PrimitivePrimSem option_Monad_Zero)a environment=Some(inr fee_empty_hash_word)).
 { rewrite (@elements_core_sem Word32(Ty.Unit+Word256)
 (fun core=>@Alg.scribe Word32(Ty.Unit+Word256)(inr fee_empty_hash_word)core)
 fee_empty_constant_parametric a environment);rewrite Alg.scribe_correct;reflexivity. }
 rewrite Constant.
 lazymatch goal with |- _ = ?rhs => change (match Elements.sem Elements.OutputScriptHash a environment,Some(inr fee_empty_hash_word) with
 | Some x,Some y=>@elements_core _ _ (fun core=>@equality_spec(Ty.Unit+Word256)core)
 (PrimitivePrimSem option_Monad_Zero)(x,y)environment|_,_=>None end=rhs) end.
 unfold Elements.sem;cbv zeta.
 destruct(nth_error(sigTxOut(Elements.envTx environment))(Z.to_nat(toZ a)))as[o|].
 all:apply elements_core_sem;apply equality_spec_parametric.
Qed.
Theorem elements_output_fee_sem a environment:
 @elements_output_fee_spec(PrimitivePrimSem option_Monad_Zero)a environment=Some(fee_spec_result a environment).
Proof.
 unfold elements_output_fee_spec;rewrite elements_comp_sem,elements_pair_sem,
 elements_output_amount_sem,elements_fee_hash_eq_reader.
 unfold amount_pair_result,fee_spec_result;destruct(nth_error(sigTxOut(Elements.envTx environment))(Z.to_nat(toZ a)))as[o|];cbn[Datatypes.option_map].
 - rewrite(elements_core_sem _ elements_fee_tail_parametric).
   rewrite elements_fee_tail_value;unfold fee_spec_bit,fee_script_hash_test.
   destruct(txoAmount o), (txoAsset o);reflexivity.
 - rewrite(elements_core_sem _ elements_fee_tail_parametric);reflexivity.
Qed.
