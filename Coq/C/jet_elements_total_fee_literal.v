(** Literal canonical totalFee program. No cached-table premise is asserted. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import Simplicity.Util.List Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import C.jet_elements_prim C.jet_elements_amount_jets C.jet_elements_asset_jets C.jet_elements_current_spec.
Require Import C.jet_elements_fee_literal C.jet_elements_prim_sem C.jet_equality_spec
 C.jet_forWhile_spec C.jet_forWhile_seq C.jet_forWhile_fold.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Set Default Timeout 10.
Definition total_fee_literal_tail {alg:Core.Algebra}:
 alg ((Ty.Unit+Bit)*((Ty.Unit+((Ty.Sum(Ty.Prod Bit Word256)Word256)*(Ty.Sum(Ty.Prod Bit Word256)Word64)))*(Word256*Word64)))
 (Word64+Word64):=
 case (injl (drop(drop(drop iden))))
 (injr (case (drop(drop(drop iden)))
   (drop(case (drop(drop iden))
     (((take(take iden)&&&injr(drop(take iden))) >>> equality_spec (Ty.Sum(Ty.Prod Bit Word256)Word256))
      &&&(take(drop iden)&&&drop(drop iden)) >>>
       case (drop(drop iden))
        (drop(case (drop iden) (Word.adder >>> drop iden)))))))).
Local Opaque equality_spec Word.adder.
Lemma total_fee_literal_tail_parametric:Core.Parametric(fun alg=>@total_fee_literal_tail alg).
Proof.
 intros a b R;unfold total_fee_literal_tail.
 repeat first[apply case_Parametric|apply injl_Parametric|apply injr_Parametric|
 apply pair_Parametric|apply comp_Parametric|apply take_Parametric|apply drop_Parametric|
 apply iden_Parametric|apply equality_spec_parametric|apply Word.adder_Parametric].
Qed.
Definition elements_total_fee_body {alg:Primitive.Algebra}:
 alg ((Word256*Word32)*Word64)(Word64+Word64):=
 elements_comp
 (elements_pair (take(drop elements_output_fee_spec))
  (elements_pair (take(drop elements_output_amount_spec)) (take(take iden)&&&drop iden)))
 (elements_core(fun core=>@total_fee_literal_tail core)).
Definition total_fee_literal_program {alg:Core.Algebra}
 (body:alg((Word256*Word32)*Word64)(Word64+Word64)):alg Word256 Word64:=
 (iden&&&(unit>>>Word.zero)) >>> for_while_program 5 body >>> copair iden iden.
Definition elements_total_fee_spec {alg:Primitive.Algebra}:alg Word256 Word64:=
 total_fee_literal_program elements_total_fee_body.

Definition total_fee_literal_step (key:tySem Word256)(acc:tySem Word64)(o:txOutput):tySem Word64:=
 match txoAsset o,txoAmount o with
 | Explicit asset,Explicit v=>
   if Bit.toBool(fee_script_hash_test o) then
    if Bit.toBool(@equality_spec Word256 CoreFunSem(key,from_hash256 asset)) then
     snd(@Word.adder 6 CoreFunSem(@fromZ (WordToZ 6)(Int64.unsigned v),acc)) else acc
   else acc
 | _,_=>acc
 end.
Local Transparent equality_spec.
Lemma total_fee_asset_eq (L R:Ty) (x y:tySem R):
 @equality_spec (Ty.Sum L R) CoreFunSem (inr x,inr y)=
 @equality_spec R CoreFunSem (y,x).
Proof. reflexivity. Qed.
Local Opaque equality_spec fee_script_hash_test from_hash256.
Lemma total_fee_literal_tail_value key acc o:
 @total_fee_literal_tail CoreFunSem
 (inr(fee_spec_bit o),(inr(encode_asset(clearPrf(txoAsset o)),encode_amount(clearPrf(txoAmount o))),(key,acc)))=
 inr(total_fee_literal_step key acc o).
Proof.
 unfold total_fee_literal_tail,total_fee_literal_step,fee_spec_bit.
 destruct(txoAsset o)as [h | [oa h] pa];destruct(txoAmount o)as [v | [ob c] pm];
 cbn [clearPrf encode_asset encode_amount].
 - destruct(fee_script_hash_test o)as [[] | []];
   cbn -[equality_spec Word.adder from_hash256].
   + reflexivity.
   + rewrite total_fee_asset_eq.
     change((inr(match @equality_spec Word256 CoreFunSem(key,from_hash256 h)with
      |inl _=>acc|inr _=>snd(@Word.adder 6 CoreFunSem(@fromZ(WordToZ 6)(Int64.unsigned v),acc))end):tySem(Word64+Word64))=
      inr(if Bit.toBool(@equality_spec Word256 CoreFunSem(key,from_hash256 h))then
       snd(@Word.adder 6 CoreFunSem(@fromZ(WordToZ 6)(Int64.unsigned v),acc))else acc)).
     destruct(@equality_spec Word256 CoreFunSem(key,from_hash256 h))as [[] | []];reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.
Lemma elements_total_fee_body_sem (key:tySem Word256)(index:tySem Word32)(acc:tySem Word64)(environment:Elements.env):
 @elements_total_fee_body (PrimitivePrimSem option_Monad_Zero) ((key,index),acc) environment=
 Some(match nth_error(sigTxOut(Elements.envTx environment))(Z.to_nat(toZ index))with
  | Some o=>inr(total_fee_literal_step key acc o)|None=>inl acc end).
Proof.
 unfold elements_total_fee_body;rewrite elements_comp_sem,!elements_pair_sem.
 lazymatch goal with |- _ = ?rhs => change
 (match (match @elements_output_fee_spec (PrimitivePrimSem option_Monad_Zero) index environment with
 |Some f=>match (match @elements_output_amount_spec (PrimitivePrimSem option_Monad_Zero) index environment with
  |Some amount=>match Some(key,acc)with Some context=>Some(amount,context)|None=>None end
  |None=>None end)with Some c=>Some(f,c)|None=>None end
 |None=>None end)with
 |Some b=>@elements_core _ _ (fun core=>@total_fee_literal_tail core)
 (PrimitivePrimSem option_Monad_Zero)b environment
 |None=>None end=rhs) end.
 rewrite elements_output_fee_sem,elements_output_amount_sem.
 unfold fee_spec_result,amount_pair_result.
 destruct(nth_error(sigTxOut(Elements.envTx environment))(Z.to_nat(toZ index)))as [o | ];
 cbn [Datatypes.option_map];rewrite(elements_core_sem _ total_fee_literal_tail_parametric).
 - rewrite total_fee_literal_tail_value;reflexivity.
 - reflexivity.
Qed.
Require Import C.jet_forWhile_fold_context.
Definition total_fee_literal_zero:tySem Word64:=@Word.zero 6 CoreFunSem tt.
Definition total_fee_literal_result (key:tySem Word256)(environment:Elements.env):tySem Word64:=
 fold_left(total_fee_literal_step key)(sigTxOut(Elements.envTx environment))total_fee_literal_zero.
Lemma elements_total_fee_run key environment:
 @for_while_run 5 Word256 Word64 Word64
 (fun p=>@elements_total_fee_body(PrimitivePrimSem option_Monad_Zero)p environment)
 key total_fee_literal_zero=Some(inl(total_fee_literal_result key environment)).
Proof.
 unfold total_fee_literal_result.
 apply (@for_while_run_fold_list_context txOutput Word256 Word64 5
  (sigTxOut(Elements.envTx environment))(total_fee_literal_step key)
  total_fee_literal_zero key).
 - pose proof(sigTxOutBounds(Elements.envTx environment))as Bound.
   change(wsize 5)with Int.modulus.
   rewrite Zlength_correct in Bound;lia.
 - intros w a;apply elements_total_fee_body_sem.
Qed.
Lemma elements_total_fee_sem (key:tySem Word256)(environment:Elements.env):
 @elements_total_fee_spec(PrimitivePrimSem option_Monad_Zero)key environment=
 Some(total_fee_literal_result key environment).
Proof.
 change(@total_fee_literal_program(CoreSem(ReaderT_CIMonad Elements.env option_CIMonad))
 (@elements_total_fee_body(PrimitivePrimSem option_Monad_Zero))key environment=
 Some(total_fee_literal_result key environment)).
 unfold total_fee_literal_program.
 assert(Zero:@Word.zero 6 (CoreSem(ReaderT_CIMonad Elements.env option_CIMonad)) tt environment=
 Some total_fee_literal_zero).
 { unfold total_fee_literal_zero;apply core_reader_sem;intros a b R;apply Word.zero_Parametric. }
 remember(@for_while_program 5 Word256 Word64 Word64
 (CoreSem(ReaderT_CIMonad Elements.env option_CIMonad))
 (@elements_total_fee_body(PrimitivePrimSem option_Monad_Zero)))as loop eqn:Loop.
 assert(Run:loop(key,total_fee_literal_zero)environment=Some(inl(total_fee_literal_result key environment))).
 { subst loop;rewrite for_while_program_reader_sem;apply elements_total_fee_run. }
 lazy beta iota zeta delta -[Word.zero total_fee_literal_result] in Zero,Run|-*.
 rewrite Zero,Run;reflexivity.
Qed.
