(** Canonical [totalFee] (Haskell/Simplicity/Elements/Programs/Transaction.hs:133)
    over the Elements primitives, and its value: the sum modulo 2^64 of the
    explicit amounts of the outputs that [outputIsFee] classifies as fees and
    whose explicit asset is the input asset.

    [totalFee = let
       body = take (drop outputIsFee) &&& (take (drop outputAmount) &&& (ooh &&& ih))
          >>> match (injl iiih)
              (injr (match iiih
               (drop (match iih
                ((ooh &&& (injr ioh) >>> eq) &&& (oih &&& iih)
                 >>> (match iih
                      (drop (match ih
                                   (add word64 >>> ih)))))))))
     in (iden &&& (unit >>> zero word64)) >>> forWhile word32 body >>> copair iden iden]

    [add word64 >>> ih] is the existing [total_adder] of the Bitcoin totals
    port and [forWhile] the existing literal [for_while_program].  No C
    execution is claimed here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Digest Simplicity.Bit.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import C.jet_elements_prim C.jet_equality_spec.
Require Import C.jet_elements_asset_jets C.jet_elements_amount_jets.
Require Import C.jet_forWhile_spec C.jet_forWhile_seq C.jet_bitcoin_totals_spec.
Require Import C.jet_elements_output_is_fee_spec.
Import ListNotations.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Local Open Scope semantic_scope.
Set Default Timeout 60.
Local Open Scope Z_scope.

Local Notation ConfTy a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).
Local Notation AmountPair := (Ty.Prod (ConfTy Word256) (ConfTy Word64)).
Module AC := Alg.Core.Combinators.

(** The pure part of [body] after its two primitive-derived components. *)
Definition total_fee_tail {alg : Core.Algebra} :
    alg (Ty.Prod (Ty.Sum Ty.Unit Bit) (Ty.Prod (Ty.Sum Ty.Unit AmountPair) (Ty.Prod Word256 Word64)))
      (Ty.Sum Word64 Word64) :=
  AC.case (AC.injl (AC.drop (AC.drop (AC.drop AC.iden))))
    (AC.injr (AC.case (AC.drop (AC.drop (AC.drop AC.iden)))
      (AC.drop (AC.case (AC.drop (AC.drop AC.iden))
        (AC.comp
          (AC.pair
            (AC.comp (AC.pair (AC.take (AC.take AC.iden)) (AC.injr (AC.drop (AC.take AC.iden))))
              (equality_spec (ConfTy Word256)))
            (AC.pair (AC.take (AC.drop AC.iden)) (AC.drop (AC.drop AC.iden))))
          (AC.case (AC.drop (AC.drop AC.iden))
            (AC.drop (AC.case (AC.drop AC.iden) total_adder)))))))).

Definition total_fee_pre {alg : Core.Algebra} :
    alg (Ty.Prod (Ty.Prod Word256 Word32) Word64) (Ty.Prod Word256 Word64) :=
  AC.pair (AC.take (AC.take AC.iden)) (AC.drop AC.iden).

Definition total_fee_body {alg : Primitive.Algebra} :
    alg (Ty.Prod (Ty.Prod Word256 Word32) Word64) (Ty.Sum Word64 Word64) :=
  AC.comp
    (AC.pair (AC.take (AC.drop elements_output_is_fee_spec))
      (AC.pair (AC.take (AC.drop elements_output_amount_spec)) total_fee_pre))
    total_fee_tail.

Definition elements_total_fee_spec {alg : Primitive.Algebra} : alg Word256 Word64 :=
  (iden &&& (unit >>> zero (n := 6))) >>> for_while_program 5 total_fee_body >>> copair iden iden.

(** * Value *)

(** The canonical contribution of one output to the fee total of asset [a]. *)
Definition canonical_fee_contrib (a : Ty.tySem Word256) (o : txOutput) : Z :=
  if canonical_fee_bit o then
    if Bit.toBool (|[ equality_spec (ConfTy Word256) ]| (encode_asset (clearPrf (txoAsset o)), inr a))
    then match clearPrf (txoAmount o) with Explicit v => Int64.unsigned v | Confidential _ _ => 0 end
    else 0
  else 0.

Definition canonical_total_fee (a : Ty.tySem Word256) (environment : Elements.env) : Z :=
  fold_right Z.add 0 (map (canonical_fee_contrib a) (sigTxOut (Elements.envTx environment))).

(** * Reader semantics *)

Lemma total_fee_tail_parametric : Core.Parametric (fun term => @total_fee_tail term).
Proof.
  intros alg1 alg2 R. unfold total_fee_tail.
  pose proof (equality_spec_parametric (ConfTy Word256) alg1 alg2 R) as HE.
  pose proof (total_adder_parametric R) as HA.
  auto 30 with parametricity.
Qed.

Lemma total_fee_pre_parametric : Core.Parametric (fun term => @total_fee_pre term).
Proof. intros alg1 alg2 R. unfold total_fee_pre. auto 10 with parametricity. Qed.

Local Notation PSem := (Primitive.CanonicalStructures.toCore (PrimitivePrimSem option_Monad_Zero)).

Lemma pcomp {A B C : Ty.Ty} (s : PSem A B) (t : PSem B C) a e :
  AC.comp s t a e = option_bind (fun b => t b e) (s a e).
Proof. cbv beta delta iota. destruct (s a e); reflexivity. Qed.
Lemma ppair {A B C : Ty.Ty} (s : PSem A B) (t : PSem A C) a e :
  AC.pair s t a e = option_bind (fun b => option_bind (fun c => Some (b, c)) (t a e)) (s a e).
Proof. cbv beta delta iota. destruct (s a e); [destruct (t a e)|]; reflexivity. Qed.
Lemma ptake {A B C : Ty.Ty} (s : PSem A C) (p : Ty.tySem (Ty.Prod A B)) e :
  AC.take (B := B) s p e = s (fst p) e.
Proof. destruct p; reflexivity. Qed.
Lemma pdrop {A B C : Ty.Ty} (s : PSem B C) (p : Ty.tySem (Ty.Prod A B)) e :
  AC.drop (A := A) s p e = s (snd p) e.
Proof. destruct p; reflexivity. Qed.

Lemma total_fee_body_reader_sem (asset : Ty.tySem Word256) (w : Ty.tySem Word32)
    (acc : Ty.tySem Word64) environment :
  @total_fee_body (PrimitivePrimSem option_Monad_Zero) ((asset, w), acc) environment =
    Some (|[ total_fee_tail ]| (canonical_fee_result w environment,
      (amount_pair_result (sigTxOut (Elements.envTx environment))
         (fun txo => clearPrf (txoAsset txo)) (fun txo => clearPrf (txoAmount txo)) w,
       (asset, acc)))).
Proof.
  assert (HT : forall x, @total_fee_tail PSem x environment = Some (|[ total_fee_tail ]| x))
    by (intro x; exact (reader_pure (E := Elements.env) (fun term => @total_fee_tail term)
      total_fee_tail_parametric x environment)).
  assert (HP : forall x, @total_fee_pre PSem x environment = Some (|[ total_fee_pre ]| x))
    by (intro x; exact (reader_pure (E := Elements.env) (fun term => @total_fee_pre term)
      total_fee_pre_parametric x environment)).
  unfold total_fee_body. rewrite pcomp, ppair, ptake, pdrop. cbn [fst snd].
  rewrite elements_output_is_fee_sem. cbn [option_bind].
  rewrite ppair, ptake, pdrop. cbn [fst snd]. rewrite elements_output_amount_sem, HP.
  unfold option_bind, option_join, option_map. cbv beta iota. rewrite HT. reflexivity.
Qed.

(** * Loop value *)

Lemma total_fee_tail_stop r2 (asset : Ty.tySem Word256) (acc : Ty.tySem Word64) :
  |[ total_fee_tail ]| (inl tt, (r2, (asset, acc))) = inl acc.
Proof. reflexivity. Qed.

Lemma total_fee_tail_fee (cA : Ty.tySem (ConfTy Word256)) (cM : Ty.tySem (ConfTy Word64))
    (asset : Ty.tySem Word256) (acc : Ty.tySem Word64) :
  |[ total_fee_tail ]| (inr (inr tt), (inr (cA, cM), (asset, acc))) =
  inr (match |[ equality_spec (ConfTy Word256) ]| (cA, inr asset) with
       | inl _ => acc
       | inr _ => match cM with inl _ => acc | inr v => |[ total_adder ]| (v, acc) end
       end).
Proof. reflexivity. Qed.

Lemma total_fee_tail_output (o : txOutput) (asset : Ty.tySem Word256) (s : Z) :
  |[ total_fee_tail ]| (inr (if canonical_fee_bit o then inr tt else inl tt),
    (inr (encode_asset (clearPrf (txoAsset o)), encode_amount (clearPrf (txoAmount o))),
     (asset, fw6 s))) =
  inr (fw6 (canonical_fee_contrib asset o + s)).
Proof.
  unfold canonical_fee_contrib.
  destruct (canonical_fee_bit o); [|reflexivity].
  rewrite total_fee_tail_fee.
  destruct (|[ equality_spec (ConfTy Word256) ]| (encode_asset (clearPrf (txoAsset o)), inr asset))
    as [u|u]; destruct u; cbn [Bit.toBool]; [reflexivity|].
  destruct (clearPrf (txoAmount o)) as [v | [odd x] p]; cbn [encode_amount]; [|reflexivity].
  unfold fw6. rewrite total_adder_fromZ. reflexivity.
Qed.

Lemma total_fee_run (asset : Ty.tySem Word256) environment :
  for_while_run 5 (fun p => @total_fee_body (PrimitivePrimSem option_Monad_Zero) p environment)
    asset (fw6 0) = Some (inl (fw6 (canonical_total_fee asset environment))).
Proof.
  set (outs := sigTxOut (Elements.envTx environment)).
  set (vals := map (canonical_fee_contrib asset) outs).
  assert (Hlen : Z.of_nat (length outs) < wsize 5).
  { pose proof (sigTxOutBounds (Elements.envTx environment)) as HB.
    rewrite Zlength_correct in HB. exact (proj2 HB). }
  assert (HS0 : fw6 0 = (fun j => fw6 (sum_first vals (Z.to_nat j))) 0)
    by (cbv beta; f_equal; destruct vals; reflexivity).
  rewrite HS0.
  refine (for_while_run_seq_left (fun j => fw6 (sum_first vals (Z.to_nat j))) 5
    (T := Z.of_nat (length outs)) (res := fw6 (canonical_total_fee asset environment)) _ asset _ _ _).
  - lia.
  - intros w Hw. cbv beta. rewrite total_fee_body_reader_sem.
    replace (0 + wz 5 w) with (wz 5 w) in * by lia.
    assert (Hn : exists o, nth_error outs (Z.to_nat (wz 5 w)) = Some o).
    { destruct (nth_error outs (Z.to_nat (wz 5 w))) as [o|] eqn:E; [exists o; reflexivity|].
      apply nth_error_None in E. pose proof (wz_range 5 w). lia. }
    destruct Hn as [o Ho].
    unfold canonical_fee_result, amount_pair_result. fold outs.
    change (@toZ (WordToZ 5) w) with (wz 5 w). rewrite Ho.
    rewrite total_fee_tail_output. f_equal. f_equal. f_equal.
    replace (Z.to_nat (wz 5 w + 1)) with (S (Z.to_nat (wz 5 w))) by (pose proof (wz_range 5 w); lia).
    assert (Hv : nth_error vals (Z.to_nat (wz 5 w)) = Some (canonical_fee_contrib asset o))
      by (unfold vals; rewrite nth_error_map, Ho; reflexivity).
    rewrite (sum_first_succ vals (Z.to_nat (wz 5 w)) Hv). lia.
  - intros w Hw. cbv beta. rewrite total_fee_body_reader_sem.
    unfold canonical_fee_result, amount_pair_result. fold outs.
    change (@toZ (WordToZ 5) w) with (wz 5 w).
    assert (Hn : nth_error outs (Z.to_nat (wz 5 w)) = None) by (apply nth_error_None; lia).
    rewrite Hn, total_fee_tail_stop. f_equal. f_equal. f_equal.
    rewrite Nat2Z.id. replace (length outs) with (length vals) by (apply map_length).
    rewrite sum_first_all. reflexivity.
Qed.

Lemma total_fee_init_parametric :
  Core.Parametric (fun term => @AC.pair Word256 Word256 Word64 term AC.iden (AC.comp AC.unit (zero (n := 6)))).
Proof. intros alg1 alg2 R. pose proof (zero_Parametric (n := 6) R). auto 10 with parametricity. Qed.

Theorem elements_total_fee_sem (a : Ty.tySem Word256) environment :
  @elements_total_fee_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (fw6 (canonical_total_fee a environment)).
Proof.
  assert (HI : @AC.pair Word256 Word256 Word64 PSem AC.iden (AC.comp AC.unit (zero (n := 6))) a environment =
      Some (a, fw6 0)).
  { refine (eq_trans (reader_pure (E := Elements.env) _ total_fee_init_parametric a environment) _).
    f_equal. }
  unfold elements_total_fee_spec. rewrite pcomp, HI.
  unfold option_bind, option_join, option_map. cbv beta iota.
  rewrite pcomp.
  assert (HF : @for_while_program 5 Word256 Word64 Word64 PSem
      (@total_fee_body (PrimitivePrimSem option_Monad_Zero)) (a, fw6 0) environment =
    for_while_run 5 (fun p => @total_fee_body (PrimitivePrimSem option_Monad_Zero) p environment)
      a (fw6 0))
    by exact (for_while_program_reader_sem 5 (E := Elements.env) (C := Word256) (B := Word64) (A := Word64)
      (@total_fee_body (PrimitivePrimSem option_Monad_Zero)) a (fw6 0) environment).
  rewrite HF, total_fee_run. reflexivity.
Qed.
