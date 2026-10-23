(** Exact optimized execution of the already sound prefix checker. *)
From Coq Require Import ZArith List.
Require Import C.jet_secp_generate_numeric C.jet_secp_generator_prefix_check C.jet_secp_generator_prefix.
Require Import C.jet_secp_generator_fast_points.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_leaf_fast base a (expected : Z*Z) :=
 let '(x,y,z):=generator_bit_fast base a true in
 let '(tx,ty):=expected in generator_normalization_fast x y z tx ty.
Lemma generator_leaf_fast_matches base a expected : generator_leaf_fast base a expected=generator_leaf_check base a expected.
Proof.
 unfold generator_leaf_fast,generator_leaf_check;rewrite generator_bit_fast_matches.
 destruct (C.jet_secp_generator_bits.literal_generate_bit base a true) as [[x y] z];
   destruct expected as [tx ty];apply generator_normalization_fast_matches.
Qed.
Fixpoint generator_prefix_fast_check depth base a (rows : list (Z*Z)) : option (list (Z*Z)) :=
 match depth with
 | Datatypes.O => match rows with []=>None | expected::tail=>if generator_leaf_fast base a expected then Some tail else None end
 | Datatypes.S k =>
     let doubled:=generator_double_fast_eval a in
     match generator_prefix_fast_check k base doubled rows with
     | None=>None
     | Some rest=>generator_prefix_fast_check k base (generator_mixed_fast_eval doubled base) rest
     end
 end.
Theorem generator_prefix_fast_check_matches depth base a rows :
 generator_prefix_fast_check depth base a rows=generator_prefix_rows_check depth base a rows.
Proof.
 revert a rows;induction depth as [|depth IH];intros a rows.
 - destruct rows as [|expected tail];[reflexivity|].
   cbn [generator_prefix_fast_check generator_prefix_rows_check];rewrite generator_leaf_fast_matches;reflexivity.
 - cbn [generator_prefix_fast_check generator_prefix_rows_check].
   rewrite generator_double_fast_eval_matches,IH.
   destruct (generator_prefix_rows_check depth base (literal_double_eval a) rows) as [rest|];[|reflexivity].
   rewrite generator_mixed_fast_eval_matches,IH;reflexivity.
Qed.
Theorem generator_prefix_fast_check_consumed depth base a rows :
 generator_prefix_fast_check depth base a rows=Some [] -> rows=generator_prefix_values depth base a.
Proof. rewrite generator_prefix_fast_check_matches;apply generator_prefix_rows_check_consumed. Qed.
