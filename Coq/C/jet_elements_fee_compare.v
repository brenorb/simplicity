(** Compare the actual empty-script C flag with the canonical literal term.
    A disagreement is characterized, not asserted reachable. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Digest.
Require Import Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jet_elements_asset_jets C.jet_elements_fee_flag_exec C.jet_elements_fee_flag_caller
 C.jet_equality_spec.
Require Import C.jet_elements_fee_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque byteStringHash from_hash256.
Definition fee_explicit_components(o:txOutput):bool:=
 match txoAsset o,txoAmount o with Explicit _,Explicit _=>Datatypes.true|_,_=>Datatypes.false end.
Lemma fee_script_hash_test_true_iff o:
 Bit.toBool(fee_script_hash_test o)=Datatypes.true <->byteStringHash(txoScript o)=byteStringHash [].
Proof.
 unfold fee_script_hash_test;rewrite equality_spec_true,fee_empty_hash_word_matches.
 split.
 - intro Same.
   pose proof(f_equal(fun x:Ty.tySem(Ty.Sum Ty.Unit Word256)=>
    match x with inl _=>byteStringHash []|inr w=>to_hash256 w end)Same)as Hash.
   change(to_hash256(from_hash256(byteStringHash(txoScript o)))=
    to_hash256(from_hash256(byteStringHash [])))in Hash.
   rewrite !to_from_hash256 in Hash;exact Hash.
 - intro Same;rewrite Same;reflexivity.
Qed.
Local Opaque fee_script_hash_test.
Lemma processed_fee_empty_true_iff o:processed_fee_empty o=Datatypes.true <->txoScript o=[].
Proof.
 unfold processed_fee_empty;destruct(txoScript o);split;intros;try reflexivity;discriminate.
Qed.
Lemma processed_fee_bit_components o:
 processed_fee_bit o=andb(fee_explicit_components o)(processed_fee_empty o).
Proof.
 unfold processed_fee_bit,fee_classifier,fee_explicit_components.
 destruct(txoAsset o)as [a | [oa a] pa];destruct(txoAmount o)as [v | [ob b] pb];
 try destruct oa;try destruct ob;destruct(processed_fee_empty o);reflexivity.
Qed.
Lemma fee_spec_bit_components o:
 Bit.toBool(fee_spec_bit o)=andb(fee_explicit_components o)(Bit.toBool(fee_script_hash_test o)).
Proof. unfold fee_spec_bit,fee_explicit_components;destruct(txoAmount o), (txoAsset o);reflexivity. Qed.
Local Opaque fee_spec_bit fee_explicit_components processed_fee_bit processed_fee_empty.
Theorem processed_fee_true_implies_literal_true o:
 processed_fee_bit o=Datatypes.true ->Bit.toBool(fee_spec_bit o)=Datatypes.true.
Proof.
 rewrite processed_fee_bit_components,fee_spec_bit_components;intros IsFee.
 apply Bool.andb_true_iff in IsFee as[Explicit Empty];rewrite Explicit;cbn.
 apply fee_script_hash_test_true_iff;apply processed_fee_empty_true_iff in Empty;rewrite Empty;reflexivity.
Qed.
Theorem processed_fee_literal_mismatch_iff o:
 processed_fee_bit o<>Bit.toBool(fee_spec_bit o) <->
 fee_explicit_components o=Datatypes.true /\txoScript o<>[] /\byteStringHash(txoScript o)=byteStringHash [].
Proof.
 rewrite processed_fee_bit_components,fee_spec_bit_components.
 destruct(fee_explicit_components o)eqn:Explicit;cbn.
 - destruct(processed_fee_empty o)eqn:Empty.
   + assert(Script:txoScript o=[])by(apply processed_fee_empty_true_iff;exact Empty).
     assert(Hash:Bit.toBool(fee_script_hash_test o)=Datatypes.true)by(apply fee_script_hash_test_true_iff;rewrite Script;reflexivity).
     rewrite Hash;split;[intro Impossible;contradiction|intros[_[NotEmpty _]];contradiction].
   + assert(NotEmpty:txoScript o<>[])by(intro Script;apply processed_fee_empty_true_iff in Script;congruence).
     destruct(Bit.toBool(fee_script_hash_test o))eqn:Hash.
     * split.
       -- intros _;split;[reflexivity|];split;[exact NotEmpty|apply fee_script_hash_test_true_iff;exact Hash].
       -- intros _;discriminate.
     * split;[intro Impossible;contradiction|].
       intros[_[_ Same]];apply fee_script_hash_test_true_iff in Same;congruence.
 - split;[intro Impossible;contradiction|intros[Impossible _];discriminate].
Qed.
Theorem output_fee_result_mismatch_iff a environment:
 processed_fee_result a environment<>fee_spec_result a environment <->
 exists o,nth_error(sigTxOut(Elements.envTx environment))(Z.to_nat(toZ a))=Some o /\
 fee_explicit_components o=Datatypes.true /\txoScript o<>[] /\byteStringHash(txoScript o)=byteStringHash [].
Proof.
 unfold processed_fee_result,fee_spec_result.
 destruct(nth_error(sigTxOut(Elements.envTx environment))(Z.to_nat(toZ a)))as[o|]eqn:Selected.
 - assert(Flag:
   (inr(if processed_fee_bit o then inr tt else inl tt):Ty.tySem(Ty.Sum Ty.Unit Bit))<>inr(fee_spec_bit o) <->
   processed_fee_bit o<>Bit.toBool(fee_spec_bit o)).
   { destruct(processed_fee_bit o);destruct(fee_spec_bit o)as[[]|[]];cbn [Bit.toBool];split;intro H;first[congruence|exfalso;exact(H eq_refl)]. }
   rewrite Flag,processed_fee_literal_mismatch_iff;split.
   + intro Bad;exists o;split;[reflexivity|exact Bad].
   + intros[o'[Same Bad]];injection Same as <-;exact Bad.
 - split.
   + intro Impossible;contradiction.
   + intros[o[Same _]];discriminate Same.
Qed.

Require Import C.jets_elements C.jet_elements_linkage C.jet_application_sep C.jet_elements_indexed_ptr.
Theorem elements_output_fee_implementation_comparison:
 application_jet_local_spec_sep f_simplicity_output_is_fee elements_ge Elements.env Word32
 (Ty.Sum Ty.Unit Bit)
 (indexed_ptr_rep(fun e=>sigTxOut(Elements.envTx e))processed_fee_rep 248 0 8 704)
 (fun a environment=>Some(processed_fee_result a environment)) /\
 forall a environment,
 (Some(processed_fee_result a environment)<>
  @elements_output_fee_spec(PrimitivePrimSem option_Monad_Zero)a environment <->
  exists o,nth_error(sigTxOut(Elements.envTx environment))(Z.to_nat(toZ a))=Some o /\
  fee_explicit_components o=Datatypes.true /\txoScript o<>[] /\byteStringHash(txoScript o)=byteStringHash []).
Proof.
 split;[exact elements_output_fee_flag_contract|];intros a environment.
 rewrite elements_output_fee_sem.
 assert(Lift:Some(processed_fee_result a environment)<>Some(fee_spec_result a environment) <->
 processed_fee_result a environment<>fee_spec_result a environment).
 { split.
 - intros NotSame Same;apply NotSame;rewrite Same;reflexivity.
 - intros NotSame Same;apply NotSame;injection Same;auto. }
 rewrite Lift;apply output_fee_result_mismatch_iff.
Qed.
