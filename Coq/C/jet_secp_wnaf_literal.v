(** Faithful structural port of wnaf15step1, wnafstepD and wnaf15 in
    Haskell/Core/Simplicity/Programs/LibSecp256k1.hs (lines 415--440, 610--611).
    The vector is most-significant first; odd digits are signed raw Word16
    values, not generator-table indices.  This is specification infrastructure
    for the C generate proof, not a public jet equivalence theorem. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_binary_spec C.jet_subtract_spec C.jet_extend_word_spec.
Require Import C.jet_full_shift_spec C.jet_word_bit_spec.
Import ListNotations.
Local Open Scope term_scope.
Set Default Timeout 10.

(** Only descend through syntactically present combinators: do not unfold a
    word operation while searching for a compositional proof. *)
Local Ltac literal_parametric_core :=
  lazymatch goal with
  | |- _ _ _ (@Alg.Core.Combinators.comp _ _ _ _ _ _) _ => apply Alg.comp_Parametric
  | |- _ _ _ (@Alg.Core.Combinators.pair _ _ _ _ _ _) _ => apply Alg.pair_Parametric
  | |- _ _ _ (@Alg.Core.Combinators.take _ _ _ _ _) _ => apply Alg.take_Parametric
  | |- _ _ _ (@Alg.Core.Combinators.drop _ _ _ _ _) _ => apply Alg.drop_Parametric
  | |- _ _ _ (@Alg.Core.Combinators.injl _ _ _ _ _) _ => apply Alg.injl_Parametric
  | |- _ _ _ (@Alg.Core.Combinators.injr _ _ _ _ _) _ => apply Alg.injr_Parametric
  | |- _ _ _ (@Alg.Core.Combinators.iden _ _) _ => apply Alg.iden_Parametric
  | |- _ _ _ (@Alg.Core.Combinators.unit _ _) _ => apply Alg.unit_Parametric
  end.

Definition literal_wnaf_state := Ty.Prod Bit (Word 7).
Definition literal_wnaf_digit := Ty.Sum Ty.Unit (Word 4).
Definition literal_wnaf_shift128 {term : Alg.Core.Algebra} :
  term literal_wnaf_state (Word 7) := @Word.full_right_shift1 Bit 7 term >>> O H.
Definition literal_wnaf_extend16 {term : Alg.Core.Algebra} :
  term (Word 4) (Word 7) := @left_extend_word_spec 4 3 term.
Definition literal_wnaf_sub128 {term : Alg.Core.Algebra} :
  term (Ty.Prod literal_wnaf_state (Word 7)) literal_wnaf_state :=
  (((O O H &&& I (@Word.leftmost Bit 7 term)) >>> @binary_bit_spec BXor term) &&&
    ((O I H &&& I H) >>> @subtract_word_spec term 7)) >>>
  ((O H &&& I O H) >>> @binary_bit_spec BXor term) &&& I I H.
Definition literal_wnaf_mask15 {term : Alg.Core.Algebra} : term (Word 4) (Word 4) :=
  O (O (O (I H &&& I H) &&& I H) &&& I H) &&& I H.
Definition literal_wnaf15_body {term : Alg.Core.Algebra} :
  term literal_wnaf_state (Ty.Prod literal_wnaf_state literal_wnaf_digit) :=
  (iden &&& (I (I I I H) >>> @literal_wnaf_mask15 term)) >>>
  (((O O H &&& O (@literal_wnaf_shift128 term)) &&&
    I (@literal_wnaf_extend16 term >>> (@Word.leftmost Bit 7 term &&& iden)
      >>> @literal_wnaf_shift128 term) >>> @literal_wnaf_sub128 term) &&& injr (I H)).
Definition literal_wnaf15_step {term : Alg.Core.Algebra} :
  term literal_wnaf_state (Ty.Prod literal_wnaf_state literal_wnaf_digit) :=
  (I (@Word.rightmost Bit 7 term) &&& iden) >>>
    Bit.cond (@literal_wnaf15_body term)
      ((O H &&& @literal_wnaf_shift128 term) &&& injl unit).
Definition literal_wnaf_double {S V : Ty} {term : Alg.Core.Algebra}
  (rec : term S (Ty.Prod S V)) : term S (Ty.Prod S (Ty.Prod V V)) :=
  rec >>> (O rec &&& I H) >>> O O H &&& (O I H &&& I H).
Fixpoint literal_wnaf_block depth {term : Alg.Core.Algebra} :
  term literal_wnaf_state (Ty.Prod literal_wnaf_state (Vector literal_wnaf_digit depth)) :=
  match depth as d return term literal_wnaf_state
    (Ty.Prod literal_wnaf_state (Vector literal_wnaf_digit d)) with
  | Datatypes.O => @literal_wnaf15_step term
  | Datatypes.S d => literal_wnaf_double (literal_wnaf_block d)
  end.
Definition literal_wnaf15_step16 {term : Alg.Core.Algebra} :=
  @literal_wnaf_block 4 term.
Definition literal_wnaf15_step128 {term : Alg.Core.Algebra} :=
  literal_wnaf_double (literal_wnaf_double (literal_wnaf_double (@literal_wnaf15_step16 term))).
Definition literal_wnaf15 {term : Alg.Core.Algebra} :
  term literal_wnaf_state (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7)) :=
  @literal_wnaf15_step128 term >>> (O (@literal_wnaf15_step term) >>> I H) &&& I H.

Lemma literal_wnaf15_step16_source {term : Alg.Core.Algebra} :
  @literal_wnaf15_step16 term = literal_wnaf_double (literal_wnaf_double
    (literal_wnaf_double (literal_wnaf_double (@literal_wnaf15_step term)))).
Proof. reflexivity. Qed.
Lemma literal_wnaf15_step128_source {term : Alg.Core.Algebra} :
  @literal_wnaf15_step128 term = @literal_wnaf_block 7 term.
Proof. reflexivity. Qed.

Lemma literal_wnaf_double_step S V (rec : Ty.Arrow S (Ty.Prod S V)) s :
  @literal_wnaf_double S V Alg.CoreFunSem rec s =
    let '(s1,v1):=rec s in let '(s2,v2):=rec s1 in (s2,(v2,v1)).
Proof.
  unfold literal_wnaf_double.
  change ((fst (rec (fst (rec s))),(snd (rec (fst (rec s))),snd (rec s)))=
    let '(a,x):=rec s in let '(b,y):=rec a in (b,(y,x))).
  destruct (rec s) as [a x];cbn [fst snd].
  destruct (rec a) as [b y];reflexivity.
Qed.


Lemma literal_wnaf15_even bit word :
  @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.zero ->
  @literal_wnaf15_step Alg.CoreFunSem (bit,word)=
    ((bit,@literal_wnaf_shift128 Alg.CoreFunSem (bit,word)),inl tt).
Proof.
  intro Even;unfold literal_wnaf15_step;change
    (match @Word.rightmost Bit 7 Alg.CoreFunSem word with
     | inl _ => ((bit,@literal_wnaf_shift128 Alg.CoreFunSem (bit,word)),inl tt)
     | inr _ => @literal_wnaf15_body Alg.CoreFunSem (bit,word)
     end=((bit,@literal_wnaf_shift128 Alg.CoreFunSem (bit,word)),inl tt));
    rewrite Even;reflexivity.
Qed.

Lemma literal_wnaf_shift128_parametric : Alg.Core.Parametric (@literal_wnaf_shift128).
Proof. intros t1 t2 R;unfold literal_wnaf_shift128;apply Alg.comp_Parametric;
  [apply Word.full_right_shift1_Parametric|apply Alg.take_Parametric;apply Alg.iden_Parametric]. Qed.
Lemma literal_wnaf_extend16_parametric : Alg.Core.Parametric (@literal_wnaf_extend16).
Proof. intros t1 t2 R;exact (left_extend_word_spec_parametric 4 3 t1 t2 R). Qed.
Lemma literal_wnaf_sub128_parametric : Alg.Core.Parametric (@literal_wnaf_sub128).
Proof.
  intros t1 t2 R;unfold literal_wnaf_sub128.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric.
    + apply Alg.comp_Parametric.
      * apply Alg.pair_Parametric.
        -- apply Alg.take_Parametric;apply Alg.take_Parametric;apply Alg.iden_Parametric.
        -- apply Alg.drop_Parametric;apply Word.leftmost_Parametric.
      * exact (binary_word_spec_parametric 0 BXor t1 t2 R).
    + apply Alg.comp_Parametric.
      * apply Alg.pair_Parametric.
        -- apply Alg.take_Parametric;apply Alg.drop_Parametric;apply Alg.iden_Parametric.
        -- apply Alg.drop_Parametric;apply Alg.iden_Parametric.
      * exact (subtract_word_spec_parametric 7 t1 t2 R).
  - apply Alg.pair_Parametric.
    + apply Alg.comp_Parametric.
      * apply Alg.pair_Parametric.
        -- apply Alg.take_Parametric;apply Alg.iden_Parametric.
        -- apply Alg.drop_Parametric;apply Alg.take_Parametric;apply Alg.iden_Parametric.
      * exact (binary_word_spec_parametric 0 BXor t1 t2 R).
    + apply Alg.drop_Parametric;apply Alg.drop_Parametric;apply Alg.iden_Parametric.
Qed.
Lemma literal_wnaf_mask15_parametric : Alg.Core.Parametric (@literal_wnaf_mask15).
Proof. intros t1 t2 R;unfold literal_wnaf_mask15;
  repeat literal_parametric_core. Qed.
Lemma literal_wnaf15_body_parametric : Alg.Core.Parametric (@literal_wnaf15_body).
Proof.
  intros t1 t2 R;unfold literal_wnaf15_body.
  repeat first [exact (literal_wnaf_mask15_parametric t1 t2 R)|
    exact (literal_wnaf_shift128_parametric t1 t2 R)|
    exact (literal_wnaf_extend16_parametric t1 t2 R)|
    exact (@Word.leftmost_Parametric t1 t2 R Bit 7)|
    exact (literal_wnaf_sub128_parametric t1 t2 R)|literal_parametric_core].
Qed.
Lemma literal_wnaf15_step_parametric : Alg.Core.Parametric (@literal_wnaf15_step).
Proof.
  intros t1 t2 R;unfold literal_wnaf15_step.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric.
    + apply Alg.drop_Parametric;apply Word.rightmost_Parametric.
    + apply Alg.iden_Parametric.
  - apply Bit.cond_Parametric.
    + exact (literal_wnaf15_body_parametric t1 t2 R).
    + repeat first [exact (literal_wnaf_shift128_parametric t1 t2 R)|literal_parametric_core].
Qed.
Lemma literal_wnaf_double_parametric {t1 t2 : Alg.Core.Algebra} (R : Alg.Core.Parametric.Rel t1 t2)
  {S V} rec1 rec2 : R S (Ty.Prod S V) rec1 rec2 ->
  R S (Ty.Prod S (Ty.Prod V V)) (literal_wnaf_double rec1) (literal_wnaf_double rec2).
Proof.
  intro Rec;unfold literal_wnaf_double;
    repeat first [exact Rec|literal_parametric_core].
Qed.
Lemma literal_wnaf_block_parametric depth : Alg.Core.Parametric (@literal_wnaf_block depth).
Proof.
  intros t1 t2 R;induction depth;cbn [literal_wnaf_block].
  - apply literal_wnaf15_step_parametric.
  - apply literal_wnaf_double_parametric;exact IHdepth.
Qed.
Lemma literal_wnaf15_parametric : Alg.Core.Parametric (@literal_wnaf15).
Proof.
  intros t1 t2 R;unfold literal_wnaf15;rewrite !literal_wnaf15_step128_source.
  repeat first [exact (literal_wnaf_block_parametric 7 t1 t2 R)|
    exact (literal_wnaf15_step_parametric t1 t2 R)|literal_parametric_core].
Qed.

Fixpoint literal_wnaf_flatten depth : Ty.tySem (Vector literal_wnaf_digit depth) ->
  list (Ty.tySem literal_wnaf_digit) :=
  match depth as d return Ty.tySem (Vector literal_wnaf_digit d) -> list (Ty.tySem literal_wnaf_digit) with
  | Datatypes.O => fun digit=>[digit]
  | Datatypes.S d => fun digits=>literal_wnaf_flatten d (fst digits)++literal_wnaf_flatten d (snd digits)
  end.
Fixpoint literal_wnaf_run count (state : Ty.tySem literal_wnaf_state) :
  Ty.tySem literal_wnaf_state * list (Ty.tySem literal_wnaf_digit) :=
  match count with
  | Datatypes.O => (state,[])
  | Datatypes.S k =>
      let '(next,digit):=@literal_wnaf15_step Alg.CoreFunSem state in
      let '(final,digits):=literal_wnaf_run k next in (final,digits++[digit])
  end.
Lemma literal_wnaf_run_add n m state :
  literal_wnaf_run (n+m) state =
    let '(middle,first):=literal_wnaf_run n state in
    let '(final,last):=literal_wnaf_run m middle in (final,last++first).
Proof.
  revert state;induction n as [|n IH];intro state.
  - cbn [Nat.add literal_wnaf_run];destruct (literal_wnaf_run m state);rewrite app_nil_r;reflexivity.
  - cbn [Nat.add literal_wnaf_run].
    destruct (@literal_wnaf15_step Alg.CoreFunSem state) as [next digit].
    rewrite IH;destruct (literal_wnaf_run n next) as [middle first];
      destruct (literal_wnaf_run m middle) as [final last];rewrite app_assoc;reflexivity.
Qed.
Lemma literal_wnaf_block_run depth state :
  (let '(final,digits):=@literal_wnaf_block depth Alg.CoreFunSem state in
    (final,literal_wnaf_flatten depth digits))=literal_wnaf_run (2^depth) state.
Proof.
  revert state;induction depth as [|depth IH];intro state.
  - cbn [literal_wnaf_block literal_wnaf_flatten literal_wnaf_run Nat.pow].
    destruct (@literal_wnaf15_step Alg.CoreFunSem state);reflexivity.
  - cbn [literal_wnaf_block];rewrite literal_wnaf_double_step.
    pose proof (IH state) as First.
    destruct (@literal_wnaf_block depth Alg.CoreFunSem state) as [middle first] eqn:E1.
    pose proof (IH middle) as Last.
    destruct (@literal_wnaf_block depth Alg.CoreFunSem middle) as [final last] eqn:E2.
    cbn [literal_wnaf_flatten fst snd] in First,Last|-*.
    replace (2^Datatypes.S depth)%nat with (2^depth+2^depth)%nat by (cbn;lia).
    rewrite literal_wnaf_run_add,<-First,<-Last;reflexivity.
Qed.
Definition literal_wnaf15_digits state :=
  let '(top,rest):=@literal_wnaf15 Alg.CoreFunSem state in top::literal_wnaf_flatten 7 rest.
Theorem literal_wnaf15_digits_order state :
  snd (literal_wnaf_run 129 state)=literal_wnaf15_digits state.
Proof.
  unfold literal_wnaf15_digits,literal_wnaf15;rewrite literal_wnaf15_step128_source.
  change (snd (literal_wnaf_run 129 state)=
    let '(middle,rest):=@literal_wnaf_block 7 Alg.CoreFunSem state in
      snd (@literal_wnaf15_step Alg.CoreFunSem middle)::literal_wnaf_flatten 7 rest).
  pose proof (literal_wnaf_block_run 7 state) as Block.
  destruct (@literal_wnaf_block 7 Alg.CoreFunSem state) as [middle rest].
  change ((middle,literal_wnaf_flatten 7 rest)=literal_wnaf_run 128 state) in Block.
  replace 129%nat with (128+1)%nat by reflexivity.
  rewrite literal_wnaf_run_add,<-Block.
  cbn [literal_wnaf_run];destruct (@literal_wnaf15_step Alg.CoreFunSem middle);reflexivity.
Qed.
Lemma literal_wnaf_flatten_length depth digits :
  length (literal_wnaf_flatten depth digits)=(2^depth)%nat.
Proof.
  revert digits;induction depth as [|depth IH];intro digits;[reflexivity|].
  destruct digits as [hi lo];cbn [literal_wnaf_flatten];rewrite app_length,!IH;cbn;lia.
Qed.
Lemma literal_wnaf_run_length count state :
  length (snd (literal_wnaf_run count state))=count.
Proof.
  revert state;induction count as [|count IH];intro state;[reflexivity|].
  cbn [literal_wnaf_run];destruct (@literal_wnaf15_step Alg.CoreFunSem state) as [next digit].
  pose proof (IH next) as Len;destruct (literal_wnaf_run count next) as [final digits].
  cbn [snd] in Len|-*;rewrite app_length.
  change ((length digits+1)%nat=Datatypes.S count).
  exact (eq_trans (f_equal (fun k=>(k+1)%nat) Len) (Nat.add_1_r count)).
Qed.
Corollary literal_wnaf15_digits_length state : length (literal_wnaf15_digits state)=129%nat.
Proof. rewrite <-literal_wnaf15_digits_order;apply literal_wnaf_run_length. Qed.

Lemma literal_wnaf_shift128_value bit word :
  @toZ (WordToZ 7) (@literal_wnaf_shift128 Alg.CoreFunSem (bit,word))=
    (((@toZ (WordToZ 0) bit)*2^128+@toZ (WordToZ 7) word)/2)%Z.
Proof.
  pose proof (full_right_word_spec_quotient 0 7 bit word) as Shift.
  change (@toZ (WordToZ 7) (@literal_wnaf_shift128 Alg.CoreFunSem (bit,word))=
    ((@toZ (WordToZ 0) bit)*2^128+@toZ (WordToZ 7) word)/2)%Z in Shift.
  exact Shift.
Qed.

Lemma literal_wnaf15_even_numeric bit word :
  Z.testbit (@toZ (WordToZ 7) word) 0=Datatypes.false ->
  @literal_wnaf15_step Alg.CoreFunSem (bit,word)=
    ((bit,@literal_wnaf_shift128 Alg.CoreFunSem (bit,word)),inl tt).
Proof.
  intro Even;apply literal_wnaf15_even.
  pose proof (word_bit_spec_numeric 7 0 word ltac:(cbn;lia)) as HBit.
  change (Bit.toBool (@Word.rightmost Bit 7 Alg.CoreFunSem word)=
    Z.testbit (@toZ (WordToZ 7) word) 0) in HBit.
  rewrite Even in HBit;destruct (@Word.rightmost Bit 7 Alg.CoreFunSem word) as [u | u];destruct u;
    [reflexivity|discriminate].
Qed.
