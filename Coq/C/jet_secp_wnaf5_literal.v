(** Faithful structural port of wnaf5step1, wnafstepD and wnaf5 in
    Haskell/Core/Simplicity/Programs/LibSecp256k1.hs (lines 413--438, 609).
    The Haskell Word4 digit is Coq [Word 2]; the state (Bit, Word128) is
    [literal_wnaf_state]. Unlike wnaf15step1, wnaf5step1 shifts before the
    parity branch, and its digit is the low nibble of the shifted word. The
    vector is most-significant first. This is specification infrastructure for
    the C point-multiplication proofs, not a public jet equivalence theorem. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_binary_spec C.jet_subtract_spec C.jet_extend_word_spec.
Require Import C.jet_full_shift_spec C.jet_word_bit_spec C.jet_secp_wnaf_literal.
Import ListNotations.
Local Open Scope term_scope.
Set Default Timeout 10.

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

Definition literal_wnaf5_digit := Ty.Sum Ty.Unit (Word 2).

(** signResize4 = left_extend word4 (five doublings): Word4 to Word128. *)
Definition literal_wnaf_extend4 {term : Alg.Core.Algebra} :
  term (Word 2) (Word 7) := @left_extend_word_spec 2 5 term.

(** body = iden &&& (drop . drop . drop $ iiih)
          >>> (oh &&& drop signResize4 >>> wnafsub128) &&& injr ih *)
Definition literal_wnaf5_body {term : Alg.Core.Algebra} :
  term literal_wnaf_state (Ty.Prod literal_wnaf_state literal_wnaf5_digit) :=
  (iden &&& (I (I (I (I I I H))))) >>>
  (((O H &&& I (@literal_wnaf_extend4 term)) >>> @literal_wnaf_sub128 term) &&& injr (I H)).

(** wnaf5step1 = drop lsb128 &&& (oh &&& fullShift128)
               >>> cond body (iden &&& injl unit) *)
Definition literal_wnaf5_step {term : Alg.Core.Algebra} :
  term literal_wnaf_state (Ty.Prod literal_wnaf_state literal_wnaf5_digit) :=
  (I (@Word.rightmost Bit 7 term) &&& (O H &&& @literal_wnaf_shift128 term)) >>>
    Bit.cond (@literal_wnaf5_body term) (iden &&& injl unit).

Fixpoint literal_wnaf5_block depth {term : Alg.Core.Algebra} :
  term literal_wnaf_state (Ty.Prod literal_wnaf_state (Vector literal_wnaf5_digit depth)) :=
  match depth as d return term literal_wnaf_state
    (Ty.Prod literal_wnaf_state (Vector literal_wnaf5_digit d)) with
  | Datatypes.O => @literal_wnaf5_step term
  | Datatypes.S d => literal_wnaf_double (literal_wnaf5_block d)
  end.
(** wnaf5step16 = wnafstepD^4 wnaf5step1; wnaf5step128 = wnafstepD^3 wnaf5step16 *)
Definition literal_wnaf5_step16 {term : Alg.Core.Algebra} :=
  literal_wnaf_double (literal_wnaf_double
    (literal_wnaf_double (literal_wnaf_double (@literal_wnaf5_step term)))).
Definition literal_wnaf5_step128 {term : Alg.Core.Algebra} :=
  literal_wnaf_double (literal_wnaf_double (literal_wnaf_double (@literal_wnaf5_step16 term))).
(** wnaf5 = wnaf5step128 >>> (take wnaf5step1 >>> ih) &&& ih *)
Definition literal_wnaf5 {term : Alg.Core.Algebra} :
  term literal_wnaf_state (Ty.Prod literal_wnaf5_digit (Vector literal_wnaf5_digit 7)) :=
  @literal_wnaf5_step128 term >>> (O (@literal_wnaf5_step term) >>> I H) &&& I H.

Lemma literal_wnaf5_step128_source {term : Alg.Core.Algebra} :
  @literal_wnaf5_step128 term = @literal_wnaf5_block 7 term.
Proof. reflexivity. Qed.

Lemma literal_wnaf5_even bit word :
  @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.zero ->
  @literal_wnaf5_step Alg.CoreFunSem (bit,word)=
    ((bit,@literal_wnaf_shift128 Alg.CoreFunSem (bit,word)),inl tt).
Proof.
  intro Even;unfold literal_wnaf5_step;change
    (match @Word.rightmost Bit 7 Alg.CoreFunSem word with
     | inl _ => ((bit,@literal_wnaf_shift128 Alg.CoreFunSem (bit,word)),inl tt)
     | inr _ => @literal_wnaf5_body Alg.CoreFunSem (bit,@literal_wnaf_shift128 Alg.CoreFunSem (bit,word))
     end=((bit,@literal_wnaf_shift128 Alg.CoreFunSem (bit,word)),inl tt));
    rewrite Even;reflexivity.
Qed.

Lemma literal_wnaf_extend4_parametric : Alg.Core.Parametric (@literal_wnaf_extend4).
Proof. intros t1 t2 R;exact (left_extend_word_spec_parametric 2 5 t1 t2 R). Qed.
Lemma literal_wnaf5_body_parametric : Alg.Core.Parametric (@literal_wnaf5_body).
Proof.
  intros t1 t2 R;unfold literal_wnaf5_body.
  repeat first [exact (literal_wnaf_extend4_parametric t1 t2 R)|
    exact (literal_wnaf_sub128_parametric t1 t2 R)|literal_parametric_core].
Qed.
Lemma literal_wnaf5_step_parametric : Alg.Core.Parametric (@literal_wnaf5_step).
Proof.
  intros t1 t2 R;unfold literal_wnaf5_step.
  apply Alg.comp_Parametric.
  - repeat first [exact (literal_wnaf_shift128_parametric t1 t2 R)|
      apply Word.rightmost_Parametric|literal_parametric_core].
  - apply Bit.cond_Parametric.
    + exact (literal_wnaf5_body_parametric t1 t2 R).
    + repeat literal_parametric_core.
Qed.
Lemma literal_wnaf5_block_parametric depth : Alg.Core.Parametric (@literal_wnaf5_block depth).
Proof.
  intros t1 t2 R;induction depth;cbn [literal_wnaf5_block].
  - apply literal_wnaf5_step_parametric.
  - apply literal_wnaf_double_parametric;exact IHdepth.
Qed.
Lemma literal_wnaf5_parametric : Alg.Core.Parametric (@literal_wnaf5).
Proof.
  intros t1 t2 R;unfold literal_wnaf5;rewrite !literal_wnaf5_step128_source.
  repeat first [exact (literal_wnaf5_block_parametric 7 t1 t2 R)|
    exact (literal_wnaf5_step_parametric t1 t2 R)|literal_parametric_core].
Qed.

(** Flattened digit order, as for wnaf15. *)
Fixpoint literal_wnaf5_flatten depth : Ty.tySem (Vector literal_wnaf5_digit depth) ->
  list (Ty.tySem literal_wnaf5_digit) :=
  match depth as d return Ty.tySem (Vector literal_wnaf5_digit d) -> list (Ty.tySem literal_wnaf5_digit) with
  | Datatypes.O => fun digit=>[digit]
  | Datatypes.S d => fun digits=>literal_wnaf5_flatten d (fst digits)++literal_wnaf5_flatten d (snd digits)
  end.
Fixpoint literal_wnaf5_run count (state : Ty.tySem literal_wnaf_state) :
  Ty.tySem literal_wnaf_state * list (Ty.tySem literal_wnaf5_digit) :=
  match count with
  | Datatypes.O => (state,[])
  | Datatypes.S k =>
      let '(next,digit):=@literal_wnaf5_step Alg.CoreFunSem state in
      let '(final,digits):=literal_wnaf5_run k next in (final,digits++[digit])
  end.
Lemma literal_wnaf5_run_add n m state :
  literal_wnaf5_run (n+m) state =
    let '(middle,first):=literal_wnaf5_run n state in
    let '(final,last):=literal_wnaf5_run m middle in (final,last++first).
Proof.
  revert state;induction n as [|n IH];intro state.
  - cbn [Nat.add literal_wnaf5_run];destruct (literal_wnaf5_run m state);rewrite app_nil_r;reflexivity.
  - cbn [Nat.add literal_wnaf5_run].
    destruct (@literal_wnaf5_step Alg.CoreFunSem state) as [next digit].
    rewrite IH;destruct (literal_wnaf5_run n next) as [middle first];
      destruct (literal_wnaf5_run m middle) as [final last];rewrite app_assoc;reflexivity.
Qed.
Lemma literal_wnaf5_block_run depth state :
  (let '(final,digits):=@literal_wnaf5_block depth Alg.CoreFunSem state in
    (final,literal_wnaf5_flatten depth digits))=literal_wnaf5_run (2^depth) state.
Proof.
  revert state;induction depth as [|depth IH];intro state.
  - cbn [literal_wnaf5_block literal_wnaf5_flatten literal_wnaf5_run Nat.pow].
    destruct (@literal_wnaf5_step Alg.CoreFunSem state);reflexivity.
  - cbn [literal_wnaf5_block];rewrite literal_wnaf_double_step.
    pose proof (IH state) as First.
    destruct (@literal_wnaf5_block depth Alg.CoreFunSem state) as [middle first] eqn:E1.
    pose proof (IH middle) as Last.
    destruct (@literal_wnaf5_block depth Alg.CoreFunSem middle) as [final last] eqn:E2.
    cbn [literal_wnaf5_flatten fst snd] in First,Last|-*.
    replace (2^Datatypes.S depth)%nat with (2^depth+2^depth)%nat by (cbn;lia).
    rewrite literal_wnaf5_run_add,<-First,<-Last;reflexivity.
Qed.
Definition literal_wnaf5_digits state :=
  let '(top,rest):=@literal_wnaf5 Alg.CoreFunSem state in top::literal_wnaf5_flatten 7 rest.
Theorem literal_wnaf5_digits_order state :
  snd (literal_wnaf5_run 129 state)=literal_wnaf5_digits state.
Proof.
  unfold literal_wnaf5_digits,literal_wnaf5;rewrite literal_wnaf5_step128_source.
  change (snd (literal_wnaf5_run 129 state)=
    let '(middle,rest):=@literal_wnaf5_block 7 Alg.CoreFunSem state in
      snd (@literal_wnaf5_step Alg.CoreFunSem middle)::literal_wnaf5_flatten 7 rest).
  pose proof (literal_wnaf5_block_run 7 state) as Block.
  destruct (@literal_wnaf5_block 7 Alg.CoreFunSem state) as [middle rest].
  change ((middle,literal_wnaf5_flatten 7 rest)=literal_wnaf5_run 128 state) in Block.
  replace 129%nat with (128+1)%nat by reflexivity.
  rewrite literal_wnaf5_run_add,<-Block.
  cbn [literal_wnaf5_run];destruct (@literal_wnaf5_step Alg.CoreFunSem middle);reflexivity.
Qed.
Lemma literal_wnaf5_run_length count state :
  length (snd (literal_wnaf5_run count state))=count.
Proof.
  revert state;induction count as [|count IH];intro state;[reflexivity|].
  cbn [literal_wnaf5_run];destruct (@literal_wnaf5_step Alg.CoreFunSem state) as [next digit].
  pose proof (IH next) as Len;destruct (literal_wnaf5_run count next) as [final digits].
  cbn [snd] in Len|-*;rewrite app_length.
  change ((length digits+1)%nat=Datatypes.S count).
  exact (eq_trans (f_equal (fun k=>(k+1)%nat) Len) (Nat.add_1_r count)).
Qed.
Corollary literal_wnaf5_digits_length state : length (literal_wnaf5_digits state)=129%nat.
Proof. rewrite <-literal_wnaf5_digits_order;apply literal_wnaf5_run_length. Qed.
