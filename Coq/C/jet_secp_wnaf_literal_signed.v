(** Literal 129-bit signed subtraction [wnafsub128] for either state sign bit.
    The literal wNAF state (b, w) denotes w - b*2^128; the subtrahend is a
    sign-extended Word128. Generalizes [literal_wnaf_sub128_positive], which
    covers b = 0 only, as needed for negative split-lambda halves. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_subtract_spec C.jet_predicate_spec C.jet_binary_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition literal_wnaf_signed_value (b : Ty.tySem Bit) (w : Ty.tySem (Word 7)) :=
  @toZ (WordToZ 7) w-2^128* @toZ BitToZ b.

Lemma literal_wnaf_sub128_shape_general b x y :
  @literal_wnaf_sub128 Alg.CoreFunSem ((b,x),y)=
    let '(borrow,payload):=@subtract_word_spec Alg.CoreFunSem 7 (x,y) in
    (@binary_bit_spec BXor Alg.CoreFunSem
      (@binary_bit_spec BXor Alg.CoreFunSem (b,@Word.leftmost Bit 7 Alg.CoreFunSem y),borrow),payload).
Proof.
  unfold literal_wnaf_sub128.
  change ((@binary_bit_spec BXor Alg.CoreFunSem
    (@binary_bit_spec BXor Alg.CoreFunSem (b,@Word.leftmost Bit 7 Alg.CoreFunSem y),
      fst (@subtract_word_spec Alg.CoreFunSem 7 (x,y))),
    snd (@subtract_word_spec Alg.CoreFunSem 7 (x,y)))=
    let '(borrow,payload):=@subtract_word_spec Alg.CoreFunSem 7 (x,y) in
    (@binary_bit_spec BXor Alg.CoreFunSem
      (@binary_bit_spec BXor Alg.CoreFunSem (b,@Word.leftmost Bit 7 Alg.CoreFunSem y),borrow),payload)).
  destruct (@subtract_word_spec Alg.CoreFunSem 7 (x,y));reflexivity.
Qed.

Theorem literal_wnaf_sub128_signed b x y :
  -2^128<=literal_wnaf_signed_value b x-
    literal_wnaf_signed_value (@Word.leftmost Bit 7 Alg.CoreFunSem y) y<2^128 ->
  exists b' payload,
    @literal_wnaf_sub128 Alg.CoreFunSem ((b,x),y)=(b',payload) /\
    literal_wnaf_signed_value b' payload=literal_wnaf_signed_value b x-
      literal_wnaf_signed_value (@Word.leftmost Bit 7 Alg.CoreFunSem y) y.
Proof.
  unfold literal_wnaf_signed_value;intro Range.
  pose proof (subtract_word_spec_numeric 7 x y) as Sub.
  pose proof (literal_wnaf_sub128_shape_general b x y) as Shape.
  destruct (@subtract_word_spec Alg.CoreFunSem 7 (x,y)) as [borrow payload] eqn:Out.
  assert (Sub' : borrow_word_balance 7 (borrow,payload)=@toZ (WordToZ 7) x-@toZ (WordToZ 7) y).
  { exact (eq_trans (eq_sym (f_equal (borrow_word_balance 7) Out)) Sub). }
  clear Sub;rename Sub' into Sub.
  assert (Shape' : @literal_wnaf_sub128 Alg.CoreFunSem ((b,x),y)=
    (@binary_bit_spec BXor Alg.CoreFunSem
      (@binary_bit_spec BXor Alg.CoreFunSem (b,@Word.leftmost Bit 7 Alg.CoreFunSem y),borrow),payload)).
  { refine (eq_trans Shape (f_equal (fun cr : Ty.tySem (Ty.Prod Bit (Word 7))=>
      let '(c,r):=cr in (@binary_bit_spec BXor Alg.CoreFunSem
        (@binary_bit_spec BXor Alg.CoreFunSem (b,@Word.leftmost Bit 7 Alg.CoreFunSem y),c),r)) Out)). }
  clear Shape;rename Shape' into Shape.
  pose proof (word_value_bounds 7 payload) as Payload.
  change (0<=@toZ (WordToZ 7) payload<2^128) in Payload.
  pose proof (word_value_bounds 7 x) as X.
  change (0<=@toZ (WordToZ 7) x<2^128) in X.
  pose proof (word_value_bounds 7 y) as Y.
  change (0<=@toZ (WordToZ 7) y<2^128) in Y.
  unfold borrow_word_balance in Sub;cbn [fst snd] in Sub.
  change (@toZ (WordToZ 7) payload-2^128* @toZ BitToZ borrow=
    @toZ (WordToZ 7) x-@toZ (WordToZ 7) y) in Sub.
  exists (@binary_bit_spec BXor Alg.CoreFunSem
    (@binary_bit_spec BXor Alg.CoreFunSem (b,@Word.leftmost Bit 7 Alg.CoreFunSem y),borrow)),payload.
  split;[exact Shape|].
  generalize dependent (@Word.leftmost Bit 7 Alg.CoreFunSem y);intros t Range Shape.
  destruct b as [u|u];destruct u;destruct t as [v|v];destruct v;
    destruct borrow as [c|c];destruct c.
  all: change (@toZ BitToZ (inl tt)) with 0 in *.
  all: change (@toZ BitToZ (inr tt)) with 1 in *.
  all: match goal with |- context [@toZ BitToZ ?t] =>
    let v:=eval vm_compute in (@toZ BitToZ t) in change (@toZ BitToZ t) with v end;lia.
Qed.
