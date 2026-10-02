(** Literal canonical Programs.TimeLock.parseLock. The subtraction-borrow
    projection is the existing canonical lt_word_spec, not a numeric substitute. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jet_order_spec C.jet_toZ C.jet_word_repr C.jet_wide C.jet_wide_spec.
Module TC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition parse_lock_threshold : Ty.tySem (Word 5) := @fromZ (WordToZ 5) 500000000.
Definition parse_lock_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word 5) (Ty.Sum (Word 5) (Word 5)) :=
  TC.comp
    (TC.pair
      (TC.comp (TC.pair TC.iden (@Alg.scribe (Word 5) (Word 5) parse_lock_threshold term))
        (@lt_word_spec term 5)) TC.iden)
    (Bit.cond (TC.injl TC.iden) (TC.injr TC.iden)).

Lemma parse_lock_spec_parametric : Alg.Core.Parametric (@parse_lock_spec).
Proof.
  intros alg1 alg2 R. unfold parse_lock_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [|apply Alg.iden_Parametric].
    apply Alg.comp_Parametric.
    + apply Alg.pair_Parametric; [apply Alg.iden_Parametric|apply Alg.scribe_Parametric].
    + apply lt_word_spec_parametric.
  - apply Bit.cond_Parametric;
      [apply Alg.injl_Parametric|apply Alg.injr_Parametric]; apply Alg.iden_Parametric.
Qed.

Lemma parse_lock_spec_numeric (x : Ty.tySem (Word 5)) :
  @parse_lock_spec Alg.CoreFunSem x =
    if @toZ (WordToZ 5) x <? 500000000 then inl x else inr x.
Proof.
  change ((match @lt_word_spec Alg.CoreFunSem 5
    (x, @Alg.scribe (Word 5) (Word 5) parse_lock_threshold Alg.CoreFunSem x) with
    | inl _ => inr x | inr _ => inl x end) =
    if @toZ (WordToZ 5) x <? 500000000 then inl x else inr x).
  rewrite Alg.scribe_correct.
  assert (HT : @toZ (WordToZ 5) parse_lock_threshold = 500000000) by (vm_compute; reflexivity).
  pose proof (lt_word_spec_numeric 5 x parse_lock_threshold) as Hlt. rewrite HT in Hlt.
  destruct (@lt_word_spec Alg.CoreFunSem 5 (x, parse_lock_threshold)) as [u | u];
    destruct u; rewrite <- Hlt; reflexivity.
Qed.

Definition parse_lock_tag r := negb (Int64.ltu r (Int64.repr 500000000)).

Lemma parse_lock_int64_denotes (x : Ty.tySem (Word 5)) r :
  Int64.unsigned r = @toZ (WordToZ 5) x ->
  (if parse_lock_tag r then inr (decode_wide W32 (Int64.zero_ext 32 r))
   else inl (decode_wide W32 (Int64.zero_ext 32 r))) = @parse_lock_spec Alg.CoreFunSem x.
Proof.
  intros Hr. assert (HD : decode_wide W32 (Int64.zero_ext 32 r) = x).
  { unfold decode_wide. rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
    change (@fromZ (WordToZ 5) (Int64.unsigned r mod 4294967296) = x).
    rewrite (word_fromZ_mod 5), Hr. apply from_toZ. }
  rewrite HD, parse_lock_spec_numeric. unfold parse_lock_tag, Int64.ltu.
  change (Int64.unsigned (Int64.repr 500000000)) with 500000000. rewrite Hr.
  destruct (Coqlib.zlt (@toZ (WordToZ 5) x) 500000000) as [Hlt|Hge]; cbn [negb].
  - assert (HL : (@toZ (WordToZ 5) x <? 500000000) = Datatypes.true) by (apply Z.ltb_lt; exact Hlt).
    rewrite HL. reflexivity.
  - assert (HL : (@toZ (WordToZ 5) x <? 500000000) = Datatypes.false) by (apply Z.ltb_ge; lia).
    rewrite HL. reflexivity.
Qed.

Lemma encode_equal_sum_word n (tag : bool) (x : Ty.tySem (Word n)) :
  @encode (Ty.Sum (Word n) (Word n)) (if tag then inr x else inl x) =
  @encode (Ty.Prod Bit (Word n)) (Bit.fromBool tag, x).
Proof.
  destruct tag; cbn [encode Bit.fromBool];
    unfold padL, padR; rewrite !Nat.sub_diag; reflexivity.
Qed.
