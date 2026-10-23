(** A single-pass, complete-consumption checker for exact signed prefixes.
    A successful result certifies the existing literal-normalized values. *)
From Coq Require Import ZArith List Lia.
Require Import C.jet_secp_generate_numeric C.jet_secp_generator_bits C.jet_secp_generator_prefix.
Require Import C.jet_secp_generator_normalization_check.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_leaf_check base a (expected : Z*Z) :=
 let '(x,y,z):=literal_generate_bit base a true in
 let '(tx,ty):=expected in generator_normalization_check x y z tx ty.
Lemma generator_leaf_check_sound base a expected : generator_leaf_check base a expected=Datatypes.true ->
 generator_odd_leaf base a=expected.
Proof.
 unfold generator_leaf_check,generator_odd_leaf.
 destruct (literal_generate_bit base a true) as [[x y] z];destruct expected as [tx ty].
 apply generator_normalization_check_sound.
Qed.

Fixpoint generator_prefix_rows_check depth base a (rows : list (Z*Z)) : option (list (Z*Z)) :=
 match depth with
 | Datatypes.O =>
     match rows with []=>None | expected::tail => if generator_leaf_check base a expected then Some tail else None end
 | Datatypes.S k =>
     let doubled:=literal_double_eval a in
     match generator_prefix_rows_check k base doubled rows with
     | None => None
     | Some rest => generator_prefix_rows_check k base (literal_mixed_eval doubled base) rest
     end
 end.

Theorem generator_prefix_rows_check_sound depth base a rows rest :
 generator_prefix_rows_check depth base a rows=Some rest ->
 rows=generator_prefix_values depth base a++rest.
Proof.
 revert a rows rest;induction depth as [|depth IH];intros a rows rest Result.
 - destruct rows as [|expected tail];[discriminate|].
   cbn [generator_prefix_rows_check] in Result.
   destruct (generator_leaf_check base a expected) eqn:Check;[|discriminate].
   injection Result as Equal;subst rest.
   cbn [generator_prefix_values app];rewrite (generator_leaf_check_sound base a expected Check);reflexivity.
 - cbn [generator_prefix_rows_check] in Result.
   destruct (generator_prefix_rows_check depth base (literal_double_eval a) rows) as [middle|] eqn:Left;
     [|discriminate].
   pose proof (IH _ _ _ Left) as LeftRows.
   pose proof (IH _ _ _ Result) as RightRows.
   cbn [generator_prefix_values];rewrite LeftRows,RightRows,app_assoc;reflexivity.
Qed.
Theorem generator_prefix_rows_check_consumed depth base a rows :
 generator_prefix_rows_check depth base a rows=Some [] -> rows=generator_prefix_values depth base a.
Proof. intro Check;rewrite (generator_prefix_rows_check_sound _ _ _ _ _ Check),app_nil_r;reflexivity. Qed.
