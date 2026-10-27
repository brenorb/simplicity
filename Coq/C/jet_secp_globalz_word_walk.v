(** Decode the checked C global-Z recurrence, retaining its indexed updates
    and first-iteration skip. This is a proof adapter, not a new jet target. *)
From Coq Require Import ZArith List Lia Ring.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_scalar_table_literal
 C.jet_secp_globalz_loop C.jet_secp_globalz_factor_call C.jet_secp_ge_zinv_arithmetic
 C.jet_secp_ge_zinv_literal C.jet_secp_rescale_literal C.jet_secp_square_columns
 C.jet_secp_square_numeric C.jet_secp_square_separate_numeric C.jet_secp_square_spec_bridge
 C.jet_secp_point_mul_numeric C.jet_secp_point_mul_storage C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_literal_spec C.jet_secp_multiply_checkpoint_columns
 C.jet_secp_negate_literal_contract.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque rescale_field_output
 literal_gej_zinv literal_fe_multiply point_mul_words square_words.

Definition globalz_word_replace (ps:nat->Ty.tySem literal_table_ge) j p k :=
 if Nat.eq_dec k j then p else ps k.
Fixpoint globalz_word_walk n (ps:nat->Ty.tySem literal_table_ge)
 (rs:nat->Ty.tySem (Word 8)) (s:Ty.tySem (Word 8)) := match n with
 | Datatypes.O=>(ps,s)
 | Datatypes.S j=>let f:=if Nat.eqb (Datatypes.S j) 7 then s else
    @literal_fe_multiply Alg.CoreFunSem (rs (Datatypes.S j),s) in
   globalz_word_walk j (globalz_word_replace ps j (@literal_gej_zinv Alg.CoreFunSem (ps j,f))) rs f
 end.
Definition globalz_decoded_points (xs ys:nat->nat->int64) (j:nat) : Ty.tySem literal_table_ge :=
 (rescale_field_output (xs j),rescale_field_output (ys j)).

Lemma globalz_decoded_residue w : radix_value w mod field_prime=
 @toZ (WordToZ 8) (rescale_field_output w) mod field_prime.
Proof.
 rewrite rescale_field_output_value,Z.mod_mod by (unfold field_prime,field_c;discriminate);reflexivity.
Qed.
Lemma globalz_multiply_commutes x y :
 @literal_fe_multiply Alg.CoreFunSem (x,y)=@literal_fe_multiply Alg.CoreFunSem (y,x).
Proof. apply (toZ_injective (WordToZ 8));rewrite !literal_multiply_numeric,Z.mul_comm;reflexivity. Qed.
Lemma globalz_factor_decoded n zs ratio : square_input_bounds zs -> square_input_bounds ratio ->
 square_input_bounds (globalz_factor_words (Z.of_nat n) zs ratio) /\
 rescale_field_output (globalz_factor_words (Z.of_nat n) zs ratio)=
 (if Nat.eqb n 7 then rescale_field_output zs else
  @literal_fe_multiply Alg.CoreFunSem (rescale_field_output ratio,rescale_field_output zs)).
Proof.
 intros BZ BR;unfold globalz_factor_words.
 destruct (Nat.eqb_spec n 7) as [->|Different].
 - split;[exact BZ|reflexivity].
 - assert (NE:Z.eqb (Z.of_nat n) 7=false) by (apply Z.eqb_neq;lia).
   rewrite NE;split;[exact (proj2 (point_mul_value_and_bounds zs ratio BZ BR))|].
   rewrite (rescale_mul_writer zs ratio _ _ BZ BR
    (globalz_decoded_residue zs) (globalz_decoded_residue ratio));apply globalz_multiply_commutes.
Qed.
Lemma globalz_scaled_bounds x y z : square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds (ge_zinv_x_words x z) /\ square_input_bounds (ge_zinv_y_words y z).
Proof.
 intros BX BY BZ;pose proof (square_result_reusable z BZ) as BS.
 pose proof (proj2 (point_mul_value_and_bounds (square_words z) z BS BZ)) as BC.
 split.
 - exact (proj2 (point_mul_value_and_bounds x (square_words z) BX BS)).
 - exact (proj2 (point_mul_value_and_bounds y (point_mul_words (square_words z) z) BY BC)).
Qed.

(** Initial point and ratio equalities are decoding relations. Every bound
    for the next state is derived from the existing arithmetic theorems. *)
Theorem globalz_walk_decoded n : (n<=7)%nat -> forall xs ys ratios zs ps rs s,
 globalz_table_bounds xs ys -> globalz_ratios_bounds ratios -> square_input_bounds zs ->
 (forall k,(k<8)%nat -> globalz_decoded_points xs ys k=ps k) ->
 (forall k,(k<8)%nat -> rescale_field_output (ratios k)=rs k) -> rescale_field_output zs=s ->
 let '((xf,yf),zf):=globalz_walk n xs ys ratios zs in
 let '(pf,sf):=globalz_word_walk n ps rs s in
 (forall k,(k<8)%nat -> globalz_decoded_points xf yf k=pf k) /\ rescale_field_output zf=sf.
Proof.
 induction n as [|j IH];intros Limit xs ys ratios zs ps rs s Bounds RatioBounds BZ Points Ratios Scale.
 - cbn [globalz_walk globalz_word_walk];split;assumption.
 - destruct (Bounds j ltac:(lia)) as [BX BY].
   destruct (globalz_factor_decoded (S j) zs (ratios (S j)) BZ (RatioBounds (S j) ltac:(lia))) as [BF Factor].
   set (f:=globalz_factor_words (Z.of_nat (S j)) zs (ratios (S j))).
   set (g:=if Nat.eqb (S j) 7 then s else @literal_fe_multiply Alg.CoreFunSem (rs (S j),s)).
   assert (Decode:rescale_field_output f=g).
   { unfold f,g;rewrite Factor,Scale,Ratios by lia;reflexivity. }
   set (xs1:=globalz_replace xs j (ge_zinv_x_words (xs j) f)).
   set (ys1:=globalz_replace ys j (ge_zinv_y_words (ys j) f)).
   set (ps1:=globalz_word_replace ps j (@literal_gej_zinv Alg.CoreFunSem (ps j,g))).
   destruct (globalz_scaled_bounds (xs j) (ys j) f BX BY BF) as [BX1 BY1].
   assert (Bounds1:globalz_table_bounds xs1 ys1).
   { intros k Range;unfold xs1,ys1,globalz_replace;destruct (Nat.eq_dec k j);[split;assumption|apply Bounds;exact Range]. }
   assert (Points1:forall k,(k<8)%nat -> globalz_decoded_points xs1 ys1 k=ps1 k).
   { intros k Range;unfold globalz_decoded_points,xs1,ys1,globalz_replace,ps1,globalz_word_replace.
     destruct (Nat.eq_dec k j) as [->|Different];[|exact (Points k Range)].
     pose proof (ge_zinv_words_literal (xs j) (ys j) f
      (rescale_field_output (xs j)) (rescale_field_output (ys j)) (rescale_field_output f)
      BX BY BF (globalz_decoded_residue _) (globalz_decoded_residue _) (globalz_decoded_residue _)) as Out.
     rewrite Decode in Out;rewrite <- (Points j ltac:(lia));exact Out. }
   cbn [globalz_walk globalz_word_walk];fold f g xs1 ys1 ps1.
   exact (IH ltac:(lia) xs1 ys1 ratios f ps1 rs g Bounds1 RatioBounds BF Points1 Ratios Decode).
Qed.
