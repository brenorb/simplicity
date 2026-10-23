(** Array/list transport for the literal-aware wNAF loop invariant. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_mask C.jet_secp_wnaf_loop.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wnaf_literal_value (digit : Ty.tySem literal_wnaf_digit) : Z :=
  match digit with inl _=>0 | inr word=>literal_wnaf_signed16 word end.
Fixpoint wnaf_slice (count : nat) (digits : Z->Z) (start : Z) : list Z :=
  match count with
  | Datatypes.O=>[]
  | Datatypes.S count=>digits start::wnaf_slice count digits (start+1)
  end.

Lemma wnaf_slice_app left right digits start :
  wnaf_slice (left+right)%nat digits start=
    wnaf_slice left digits start++wnaf_slice right digits (start+Z.of_nat left).
Proof.
  revert start;induction left as [|left IH];intro start.
  - cbn [Nat.add wnaf_slice];rewrite Z.add_0_r;reflexivity.
  - cbn [Nat.add wnaf_slice];rewrite IH.
    assert (Start : start+1+Z.of_nat left=start+Z.of_nat (S left)) by (rewrite Nat2Z.inj_succ;lia).
    rewrite Start;reflexivity.
Qed.

Lemma wnaf_slice_ext count a b start :
  (forall i, start<=i<start+Z.of_nat count -> a i=b i) ->
  wnaf_slice count a start=wnaf_slice count b start.
Proof.
  revert start;induction count as [|count IH];intros start Same;[reflexivity|].
  cbn [wnaf_slice];f_equal.
  - apply Same;rewrite Nat2Z.inj_succ;pose proof (Nat2Z.is_nonneg count);lia.
  - apply IH;intros i Range;apply Same;rewrite Nat2Z.inj_succ;lia.
Qed.

Lemma wnaf_slice_constant count digits start value :
  (forall i, start<=i<start+Z.of_nat count -> digits i=value) ->
  wnaf_slice count digits start=repeat value count.
Proof.
  revert start;induction count as [|count IH];intros start Same;[reflexivity|].
  cbn [wnaf_slice repeat];f_equal.
  - apply Same;rewrite Nat2Z.inj_succ;pose proof (Nat2Z.is_nonneg count);lia.
  - apply IH;intros i Range;apply Same;rewrite Nat2Z.inj_succ;lia.
Qed.

Lemma wnaf_slice_update count digits start value :
  (forall i, start<=i<start+Z.of_nat (S count) -> digits i=0) ->
  wnaf_slice (S count) (wnaf_update digits start value) start=value::repeat 0 count.
Proof.
  intro Zero;cbn [wnaf_slice];f_equal.
  - unfold wnaf_update;destruct Coqlib.zeq;[reflexivity|contradiction].
  - apply wnaf_slice_constant;intros i Range.
    unfold wnaf_update;destruct Coqlib.zeq;[lia|apply Zero;rewrite Nat2Z.inj_succ;lia].
Qed.

Lemma wnaf_slice_seq count digits start :
  wnaf_slice count digits start=map (fun i=>digits (start+Z.of_nat i)) (seq 0 count).
Proof.
  revert start;induction count as [|count IH];intro start;[reflexivity|].
  cbn [wnaf_slice seq map];rewrite Z.add_0_r,IH;f_equal.
  rewrite <-seq_shift,map_map;apply map_ext;intro i.
  rewrite Nat2Z.inj_succ;f_equal;lia.
Qed.

Lemma wnaf_literal_segment count digit :
  map wnaf_literal_value (repeat (inl tt) count++[inr digit])=
    repeat 0 count++[literal_wnaf_signed16 digit].
Proof. rewrite map_app,map_repeat;reflexivity. Qed.

Lemma wnaf_literal_run_join left right state next segment :
  literal_wnaf_run left state=(next,segment) ->
  map wnaf_literal_value (snd (literal_wnaf_run (left+right)%nat state))=
    map wnaf_literal_value (snd (literal_wnaf_run right next))++map wnaf_literal_value segment.
Proof.
  intro First;rewrite literal_wnaf_run_add,First.
  destruct (literal_wnaf_run right next);cbn [snd];apply map_app.
Qed.
