(** Literal Programs.TimeLock.parseSequence and its symbolic bit/word view.
    This prepares an actual C-call proof; it does not add jet coverage. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers Coqlib.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jet_word_repr C.jet_word_bit_spec.
Require Import C.jet_int64_bit_mask C.jet_wide C.jet_wide_spec.
Import ListNotations.
Module SC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition parse_sequence_bit31 {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word 5) Bit :=
  SC.take (SC.take (SC.take (SC.take (SC.take SC.iden)))).
Definition parse_sequence_bit22 {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word 5) Bit :=
  SC.take (SC.drop (SC.take (SC.take (SC.drop SC.iden)))).
Definition parse_sequence_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word 5) (Ty.Sum Ty.Unit (Ty.Sum (Word 4) (Word 4))) :=
  SC.comp
    (SC.pair parse_sequence_bit31 (SC.pair parse_sequence_bit22 (SC.drop SC.iden)))
    (Bit.cond (SC.injl SC.unit)
      (SC.injr (Bit.cond (SC.injr SC.iden) (SC.injl SC.iden)))).

Lemma parse_sequence_spec_parametric : Alg.Core.Parametric (@parse_sequence_spec).
Proof.
  intros alg1 alg2 R. unfold parse_sequence_spec, parse_sequence_bit31, parse_sequence_bit22.
  repeat first [apply Alg.comp_Parametric | apply Alg.pair_Parametric | apply Bit.cond_Parametric
    | apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.injl_Parametric
    | apply Alg.injr_Parametric | apply Alg.iden_Parametric | apply Alg.unit_Parametric].
Qed.

Definition parse_sequence_enabled r :=
  Int64.ltu r (Int64.shl Int64.one (Int64.repr 31)).
Definition parse_sequence_tag r :=
  negb (Int64.eq (Int64.and r (Int64.shl Int64.one (Int64.repr 22))) Int64.zero).
Definition parse_sequence_payload r := Int64.and r (Int64.repr 65535).

Lemma parse_sequence_enabled_bit31 (x : Ty.tySem (Word 5)) r :
  Int64.unsigned r = @toZ (WordToZ 5) x ->
  parse_sequence_enabled r = negb (Z.testbit (@toZ (WordToZ 5) x) 31).
Proof.
  intros Hr. pose proof (word_toZ_range 5 x) as HX.
  rewrite (top_bit_threshold (@toZ (WordToZ 5) x) 31 ltac:(lia) HX), negb_involutive.
  unfold parse_sequence_enabled, Int64.ltu.
  assert (HS : Int64.shl Int64.one (Int64.repr 31) = Int64.repr 2147483648) by (vm_compute; reflexivity).
  rewrite HS, Hr. change (Int64.unsigned (Int64.repr 2147483648)) with 2147483648.
  change (2 ^ 31) with 2147483648.
  destruct (zlt (@toZ (WordToZ 5) x) 2147483648) as [Hlt|Hge].
  - symmetry. apply Z.ltb_lt; exact Hlt.
  - symmetry. apply Z.ltb_ge; lia.
Qed.

Lemma parse_sequence_tag_bit22 (x : Ty.tySem (Word 5)) r :
  Int64.unsigned r = @toZ (WordToZ 5) x ->
  parse_sequence_tag r = Z.testbit (@toZ (WordToZ 5) x) 22.
Proof.
  intros Hr. unfold parse_sequence_tag.
  assert (HS : Int64.shl Int64.one (Int64.repr 22) = Int64.repr (2 ^ 22)) by (vm_compute; reflexivity).
  rewrite HS, int64_single_bit_mask_nonzero by lia. unfold Int64.testbit. rewrite Hr. reflexivity.
Qed.

Lemma parse_sequence_payload_decode r :
  decode_wide W16 (Int64.zero_ext 16 (parse_sequence_payload r)) =
    @fromZ (WordToZ 4) (Int64.unsigned r).
Proof.
  unfold parse_sequence_payload, decode_wide.
  assert (HM : Int64.and r (Int64.repr 65535) = Int64.zero_ext 16 r).
  { symmetry. apply Int64.zero_ext_and; lia. }
  rewrite HM, Int64.zero_ext_idem by lia.
  rewrite Int64.zero_ext_mod by (change (0 <= 16 < 64); lia).
  change (@fromZ (WordToZ 4) (Int64.unsigned r mod 65536) = @fromZ (WordToZ 4) (Int64.unsigned r)).
  apply (word_fromZ_mod 4).
Qed.

Lemma parse_sequence_bit31_projection {term : Alg.Core.Algebra} :
  @parse_sequence_bit31 term = @word_bit_spec 5 31 term.
Proof. reflexivity. Qed.
Lemma parse_sequence_bit22_projection {term : Alg.Core.Algebra} :
  @parse_sequence_bit22 term = @word_bit_spec 5 22 term.
Proof. reflexivity. Qed.

Lemma parse_sequence_spec_value (x : Ty.tySem (Word 5)) :
  @parse_sequence_spec Alg.CoreFunSem x =
  if Bit.toBool (@parse_sequence_bit31 Alg.CoreFunSem x) then inl tt
  else inr (if Bit.toBool (@parse_sequence_bit22 Alg.CoreFunSem x) then inr (snd x) else inl (snd x)).
Proof.
  change ((match @parse_sequence_bit31 Alg.CoreFunSem x with
    | inl _ => inr (match @parse_sequence_bit22 Alg.CoreFunSem x with
        | inl _ => inl (snd x) | inr _ => inr (snd x) end)
    | inr _ => inl tt end) =
    if Bit.toBool (@parse_sequence_bit31 Alg.CoreFunSem x) then inl tt
    else inr (if Bit.toBool (@parse_sequence_bit22 Alg.CoreFunSem x)
      then inr (snd x) else inl (snd x))).
  destruct (@parse_sequence_bit31 Alg.CoreFunSem x) as [u | u]; destruct u;
    destruct (@parse_sequence_bit22 Alg.CoreFunSem x) as [v | v]; destruct v; reflexivity.
Qed.

Lemma parse_sequence_low16 (x : Ty.tySem (Word 5)) :
  @fromZ (WordToZ 4) (@toZ (WordToZ 5) x) = snd x.
Proof.
  destruct x as [hi lo]. apply (proj2 (word_fromZ_bits 4 lo _)).
  intros j Hj. apply testbitToZLo. change (j < 16). exact (proj2 Hj).
Qed.

Lemma parse_sequence_spec_numeric (x : Ty.tySem (Word 5)) :
  @parse_sequence_spec Alg.CoreFunSem x =
  if Z.testbit (@toZ (WordToZ 5) x) 31 then inl tt
  else inr (if Z.testbit (@toZ (WordToZ 5) x) 22
    then inr (@fromZ (WordToZ 4) (@toZ (WordToZ 5) x))
    else inl (@fromZ (WordToZ 4) (@toZ (WordToZ 5) x))).
Proof.
  rewrite parse_sequence_spec_value, parse_sequence_bit31_projection, parse_sequence_bit22_projection.
  rewrite (word_bit_spec_numeric 5 31 x ltac:(change (31 < 32)%nat; lia)).
  rewrite (word_bit_spec_numeric 5 22 x ltac:(change (22 < 32)%nat; lia)).
  rewrite parse_sequence_low16. reflexivity.
Qed.

Lemma parse_sequence_int64_denotes (x : Ty.tySem (Word 5)) r :
  Int64.unsigned r = @toZ (WordToZ 5) x ->
  (if parse_sequence_enabled r then
     inr (if parse_sequence_tag r
       then inr (decode_wide W16 (Int64.zero_ext 16 (parse_sequence_payload r)))
       else inl (decode_wide W16 (Int64.zero_ext 16 (parse_sequence_payload r))))
   else inl tt) = @parse_sequence_spec Alg.CoreFunSem x.
Proof.
  intros Hr. rewrite (parse_sequence_enabled_bit31 x r Hr), (parse_sequence_tag_bit22 x r Hr),
    parse_sequence_payload_decode, Hr, parse_sequence_spec_numeric.
  destruct (Z.testbit (@toZ (WordToZ 5) x) 31); reflexivity.
Qed.

Lemma encode_parse_sequence_disabled :
  @encode (Ty.Sum Ty.Unit (Ty.Sum (Word 4) (Word 4))) (inl tt) =
    Some Datatypes.false :: repeat None 17.
Proof. reflexivity. Qed.

Lemma encode_parse_sequence_enabled (tag : bool) (x : Ty.tySem (Word 4)) :
  @encode (Ty.Sum Ty.Unit (Ty.Sum (Word 4) (Word 4)))
    (inr (if tag then inr x else inl x)) =
    Some Datatypes.true :: Some tag :: encode x.
Proof. destruct tag; reflexivity. Qed.
