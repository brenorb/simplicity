(** The magnitude-one Y bound required by the original signed table lookup.
    The last Y is weak-normalized and every other Y is a product output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_field_mul_small C.jet_secp_square_columns C.jet_secp_square_execution
 C.jet_secp_square_separate_numeric
 C.jet_secp_point_mul_numeric C.jet_secp_point_mul_storage C.jet_secp_ge_zinv_arithmetic
 C.jet_secp_double_coordinate_numeric C.jet_secp_globalz_loop C.jet_secp_globalz_factor_call
 C.jet_secp_globalz_function C.jet_secp_globalz_word_walk C.jet_secp_globalz_pass2
 C.jet_secp_field_weak_loose C.jet_secp_rescale_literal.
Set Default Timeout 10.
Local Open Scope Z_scope.

Lemma globalz_scaled_y_tight y z : square_input_bounds y -> square_input_bounds z ->
 mul_small_input_bounds (ge_zinv_y_words y z).
Proof.
 intros BY BZ;unfold ge_zinv_y_words;apply double_mul_tight;[exact BY|].
 apply (proj2 (point_mul_value_and_bounds _ _ (square_result_reusable z BZ) BZ)).
Qed.
Local Opaque ge_zinv_y_words.

Theorem globalz_walk_tight_y n : (n<=7)%nat -> forall xs ys ratios zs,
 globalz_table_bounds xs ys -> globalz_ratios_bounds ratios -> square_input_bounds zs ->
 (forall k,(n<=k<8)%nat -> mul_small_input_bounds (ys k)) ->
 let '((xf,yf),zf):=globalz_walk n xs ys ratios zs in
 forall k,(k<8)%nat -> mul_small_input_bounds (yf k).
Proof.
 induction n as [|j IH];intros Limit xs ys ratios zs Bounds RatioBounds BZ Tight.
 - cbn [globalz_walk];intros k Range;apply Tight;lia.
 - destruct (Bounds j ltac:(lia)) as [BX BY].
   destruct (globalz_factor_decoded (S j) zs (ratios (S j)) BZ (RatioBounds (S j) ltac:(lia))) as [BF Factor].
   set (f:=globalz_factor_words (Z.of_nat (S j)) zs (ratios (S j))).
   set (xs1:=globalz_replace xs j (ge_zinv_x_words (xs j) f)).
   set (ys1:=globalz_replace ys j (ge_zinv_y_words (ys j) f)).
   destruct (globalz_scaled_bounds (xs j) (ys j) f BX BY BF) as [BX1 BY1].
   assert (Bounds1:globalz_table_bounds xs1 ys1).
   { intros k Range;unfold xs1,ys1,globalz_replace;destruct (Nat.eq_dec k j);[split;assumption|apply Bounds;exact Range]. }
   assert (Tight1:forall k,(j<=k<8)%nat -> mul_small_input_bounds (ys1 k)).
   { intros k Range;unfold ys1,globalz_replace;destruct (Nat.eq_dec k j) as [->|Different].
     - apply globalz_scaled_y_tight;assumption.
     - apply Tight;lia. }
   cbn [globalz_walk];fold f xs1 ys1.
   exact (IH ltac:(lia) xs1 ys1 ratios f Bounds1 RatioBounds BF Tight1).
Qed.

Corollary globalz_eight_tight_y xs ys ratios :
 globalz_table_bounds xs ys -> globalz_ratios_bounds ratios ->
 let '((xf,yf),zf):=globalz_walk 7 xs (globalz_start_ys ys) ratios (ratios 7%nat) in
 forall k,(k<8)%nat -> mul_small_input_bounds (yf k).
Proof.
 intros Bounds RatioBounds.
 apply globalz_walk_tight_y;[lia|apply globalz_start_bounds;exact Bounds|exact RatioBounds|apply RatioBounds;lia|].
 intros k Range;assert (k=7)%nat by lia;subst k.
 unfold globalz_start_ys,globalz_replace;destruct (Nat.eq_dec 7 7) as [_|N];[|contradiction].
 apply (proj2 (weak_loose_numeric _ (rescale_writer_bounds _ (proj2 (Bounds 7%nat ltac:(lia)))))).
Qed.
