(** Canonical specification of the Bitcoin input_value jet: the literal
    primitive InputValue, with its Option-to-Sum result and Word32 index. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Import Simplicity.Primitive.Bitcoin C.jet_wide_spec C.jet_wide C.jet_word_repr.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 30.

Definition bitcoin_input_value_spec {alg : Primitive.Algebra} : alg Word32 (Ty.Sum Ty.Unit Word64) :=
  Primitive.Combinators.prim Bitcoin.InputValue.

Lemma bitcoin_input_value_spec_parametric : Primitive.Parametric (@bitcoin_input_value_spec).
Proof. intros alg1 alg2 R. apply prim_Parametric. Qed.

Definition bitcoin_input_value_result (environment : Bitcoin.env) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit Word64) :=
  match nth_error (sigTxIn (Bitcoin.envTx environment)) (Z.to_nat (toZ a)) with
  | Some txi => inr (@fromZ (WordToZ 6) (Int64.signed (sigTxiValue txi)))
  | None => inl tt
  end.

Lemma bitcoin_input_value_spec_sem (environment : Bitcoin.env) a :
  @bitcoin_input_value_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (bitcoin_input_value_result environment a).
Proof.
  assert (H : @bitcoin_input_value_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Bitcoin.sem Bitcoin.InputValue a environment) by reflexivity.
  rewrite H. unfold Bitcoin.sem, bitcoin_input_value_result. cbv zeta.
  destruct (nth_error (sigTxIn (Bitcoin.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Lemma encode_sum_inr_word64 (w : Ty.tySem Word64) :
  @encode (Ty.Sum Ty.Unit Word64) (inr w) = Some true :: @encode Word64 w.
Proof. reflexivity. Qed.

Lemma encode_sum_inl_word64 :
  @encode (Ty.Sum Ty.Unit Word64) (inl tt) = Some false :: repeat None 64.
Proof. vm_compute. reflexivity. Qed.

(** Both integer views encode the same canonical Word64, including values
    whose most significant bit is set.  No monetary range is required. *)
Lemma word64_signed_unsigned v :
  @fromZ (WordToZ 6) (Int64.signed v) =
  @fromZ (WordToZ 6) (Int64.unsigned v).
Proof.
  rewrite <- (word_fromZ_mod 6 (Int64.signed v)).
  change (@fromZ (WordToZ 6) (Int64.signed v mod Int64.modulus) =
    @fromZ (WordToZ 6) (Int64.unsigned v)).
  rewrite <- Int64.unsigned_repr_eq, Int64.repr_signed. reflexivity.
Qed.

Lemma decode_wide64_value v :
  decode_wide W64 (Int64.zero_ext 64 v) = @fromZ (WordToZ 6) (Int64.signed v).
Proof.
  unfold decode_wide. change (wide_log W64) with 6%nat.
  rewrite Int64.zero_ext_above by (change Int64.zwordsize with 64; lia).
  symmetry. apply word64_signed_unsigned.
Qed.

(** Retained as a compatibility corollary; the stronger result above covers
    every machine value. *)
Lemma decode_wide64_money v :
  0 <= Int64.signed v ->
  decode_wide W64 (Int64.zero_ext 64 v) = @fromZ (WordToZ 6) (Int64.signed v).
Proof.
  intros _. apply decode_wide64_value.
Qed.
