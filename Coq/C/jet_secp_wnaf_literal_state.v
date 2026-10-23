(** Literal signed subtraction in the positive residual range used by generate.
    This discharges one part of the odd-step state bridge, not that whole
    bridge or a public jet theorem. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_subtract_spec C.jet_predicate_spec C.jet_binary_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma literal_wnaf_sub128_shape x y :
  @literal_wnaf_sub128 Alg.CoreFunSem ((Bit.zero,x),y)=
    let '(borrow,payload):=@subtract_word_spec Alg.CoreFunSem 7 (x,y) in
    (@binary_bit_spec BXor Alg.CoreFunSem
      (@binary_bit_spec BXor Alg.CoreFunSem (Bit.zero,@Word.leftmost Bit 7 Alg.CoreFunSem y),borrow),payload).
Proof.
  unfold literal_wnaf_sub128.
  change ((@binary_bit_spec BXor Alg.CoreFunSem
    (@binary_bit_spec BXor Alg.CoreFunSem (Bit.zero,@Word.leftmost Bit 7 Alg.CoreFunSem y),
      fst (@subtract_word_spec Alg.CoreFunSem 7 (x,y))),
    snd (@subtract_word_spec Alg.CoreFunSem 7 (x,y)))=
    let '(borrow,payload):=@subtract_word_spec Alg.CoreFunSem 7 (x,y) in
    (@binary_bit_spec BXor Alg.CoreFunSem
      (@binary_bit_spec BXor Alg.CoreFunSem (Bit.zero,@Word.leftmost Bit 7 Alg.CoreFunSem y),borrow),payload)).
  destruct (@subtract_word_spec Alg.CoreFunSem 7 (x,y));reflexivity.
Qed.

Theorem literal_wnaf_sub128_positive x y :
  0<=@toZ (WordToZ 7) x-@toZ (WordToZ 7) y+
      2^128* @toZ BitToZ (@Word.leftmost Bit 7 Alg.CoreFunSem y)<2^128 ->
  exists payload : Ty.tySem (Word 7),
    @literal_wnaf_sub128 Alg.CoreFunSem ((Bit.zero,x),y)=(Bit.zero,payload) /\
    @toZ (WordToZ 7) payload=@toZ (WordToZ 7) x-@toZ (WordToZ 7) y+
      2^128* @toZ BitToZ (@Word.leftmost Bit 7 Alg.CoreFunSem y).
Proof.
  intro Range.
  pose proof (subtract_word_spec_numeric 7 x y) as Sub.
  pose proof (literal_wnaf_sub128_shape x y) as Shape.
  destruct (@subtract_word_spec Alg.CoreFunSem 7 (x,y)) as [borrow payload] eqn:Out.
  assert (Sub' : borrow_word_balance 7 (borrow,payload)=@toZ (WordToZ 7) x-@toZ (WordToZ 7) y).
  { exact (eq_trans (eq_sym (f_equal (borrow_word_balance 7) Out)) Sub). }
  clear Sub;rename Sub' into Sub.
  assert (Shape' : @literal_wnaf_sub128 Alg.CoreFunSem ((Bit.zero,x),y)=
    (@binary_bit_spec BXor Alg.CoreFunSem
      (@binary_bit_spec BXor Alg.CoreFunSem (Bit.zero,@Word.leftmost Bit 7 Alg.CoreFunSem y),borrow),payload)).
  { refine (eq_trans Shape (f_equal (fun cr : Ty.tySem (Ty.Prod Bit (Word 7))=>
      let '(b,r):=cr in (@binary_bit_spec BXor Alg.CoreFunSem
        (@binary_bit_spec BXor Alg.CoreFunSem (Bit.zero,@Word.leftmost Bit 7 Alg.CoreFunSem y),b),r)) Out)). }
  clear Shape;rename Shape' into Shape.
  pose proof (word_value_bounds 7 payload) as Payload.
  change (0<=@toZ (WordToZ 7) payload<2^128) in Payload.
  unfold borrow_word_balance in Sub;cbn [fst snd] in Sub.
  change (@toZ (WordToZ 7) payload-2^128* @toZ BitToZ borrow=
    @toZ (WordToZ 7) x-@toZ (WordToZ 7) y) in Sub.
  destruct (@Word.leftmost Bit 7 Alg.CoreFunSem y) as [u|u];destruct u;
    destruct borrow as [v|v];destruct v.
  all: try change (@toZ BitToZ Bit.zero) with 0 in *.
  all: try change (@toZ BitToZ Bit.one) with 1 in *.
  - exists payload;split;[exact Shape|lia].
  - lia.
  - lia.
  - exists payload;split;[exact Shape|lia].
Qed.
