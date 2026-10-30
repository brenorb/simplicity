(** Bind the four Horner coefficients to the actual literal window outputs. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_strauss_scalar_group C.jet_secp_strauss_program
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf_literal C.jet_secp_wnaf5_signed_array
 C.jet_secp_wnaf_literal_array C.jet_secp_wnaf5_reconstruction C.jet_secp_wnaf15_reconstruction.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma secp_combine_maps {A B:Type} (xs:list A) (ys:list B):
 length xs=length ys ->map fst (combine xs ys)=xs /\map snd (combine xs ys)=ys.
Proof.
 revert ys;induction xs as [|x xs IH];intros [|y ys] Length;cbn [length] in Length;
 cbn [combine map];try discriminate.
 - split;reflexivity.
 - destruct (IH ys ltac:(lia)) as [Left Right];split;f_equal;assumption.
Qed.
Lemma secp_fold_left_map {A B C:Type} (step:C->B->C) (f:A->B) xs c:
 fold_left (fun acc x=>step acc (f x)) xs c=fold_left step (map f xs) c.
Proof. revert c;induction xs as [|x xs IH];intro c;[reflexivity|cbn [fold_left map];apply IH]. Qed.
Lemma secp_strauss_four_maps
 (xs ys:list (Ty.tySem literal_wnaf5_digit)) (gs hs:list (Ty.tySem literal_wnaf_digit)):
 length xs=length ys ->length gs=length hs ->length xs=length gs ->
 let ds:=combine (combine xs ys) (combine gs hs) in
 map (fun d=>fst (fst d)) ds=xs /\map (fun d=>snd (fst d)) ds=ys /\
 map (fun d=>fst (snd d)) ds=gs /\map (fun d=>snd (snd d)) ds=hs.
Proof.
 intros XY GH XG;cbn zeta.
 destruct (secp_combine_maps xs ys XY) as [PointL PointR].
 destruct (secp_combine_maps gs hs GH) as [GenL GenR].
 assert (Outer:length (combine xs ys)=length (combine gs hs)).
 { rewrite !combine_length,<-XY,<-GH,!Nat.min_id;exact XG. }
 destruct (secp_combine_maps (combine xs ys) (combine gs hs) Outer) as [Left Right].
 split.
 - transitivity (map fst (map fst (combine (combine xs ys) (combine gs hs)))).
   + symmetry;apply map_map.
   + rewrite Left;exact PointL.
 - split.
   + transitivity (map snd (map fst (combine (combine xs ys) (combine gs hs)))).
     * symmetry;apply map_map.
     * rewrite Left;exact PointR.
   + split.
     * transitivity (map fst (map snd (combine (combine xs ys) (combine gs hs)))).
       { symmetry;apply map_map. }
       rewrite Right;exact GenL.
     * transitivity (map snd (map snd (combine (combine xs ys) (combine gs hs)))).
       { symmetry;apply map_map. }
       rewrite Right;exact GenR.
Qed.
Lemma secp_wnaf5_flatten_length depth digits:
 length (literal_wnaf5_flatten depth digits)=(2^depth)%nat.
Proof.
 revert digits;induction depth as [|depth IH];intro digits;[reflexivity|].
 destruct digits as [hi lo];cbn [literal_wnaf5_flatten];rewrite app_length,!IH;cbn;lia.
Qed.
Lemma secp_strauss_coefficient_projected
 (digits:list (Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit))):
 fold_left secp_strauss_coefficient_step digits ((0,0),(0,0))=
 ((fold_left secp_wnaf5_digit_fold (map (fun d=>fst (fst d)) digits) 0,
   fold_left secp_wnaf5_digit_fold (map (fun d=>snd (fst d)) digits) 0),
  (fold_left secp_wnaf15_digit_fold (map (fun d=>fst (snd d)) digits) 0,
   fold_left secp_wnaf15_digit_fold (map (fun d=>snd (snd d)) digits) 0)).
Proof.
 rewrite secp_strauss_coefficient_fold_values;apply f_equal2.
 - apply f_equal2.
   + exact (secp_fold_left_map secp_wnaf5_digit_fold
      (fun d:Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit)=>fst (fst d)) digits 0).
   + exact (secp_fold_left_map secp_wnaf5_digit_fold
      (fun d:Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit)=>snd (fst d)) digits 0).
 - apply f_equal2.
   + exact (secp_fold_left_map secp_wnaf15_digit_fold
      (fun d:Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit)=>fst (snd d)) digits 0).
   + exact (secp_fold_left_map secp_wnaf15_digit_fold
      (fun d:Ty.tySem (literal_strauss_windows literal_wnaf5_digit literal_wnaf_digit)=>snd (snd d)) digits 0).
Qed.
Local Opaque literal_wnaf5_flatten literal_wnaf_flatten literal_wnaf5 literal_wnaf15.
Lemma secp_strauss_merged_coefficients
 (h1 hl:Ty.tySem literal_wnaf5_digit) (t1 tl:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hg hh:Ty.tySem literal_wnaf_digit) (tg th:Ty.tySem (Vector literal_wnaf_digit 7)):
 fold_left secp_strauss_coefficient_step
  (((h1,hl),(hg,hh))::
    combine (combine (literal_wnaf5_flatten 7 t1) (literal_wnaf5_flatten 7 tl))
     (combine (literal_wnaf_flatten 7 tg) (literal_wnaf_flatten 7 th))) ((0,0),(0,0))=
 ((fold_left secp_wnaf5_digit_fold (h1::literal_wnaf5_flatten 7 t1) 0,
   fold_left secp_wnaf5_digit_fold (hl::literal_wnaf5_flatten 7 tl) 0),
  (fold_left secp_wnaf15_digit_fold (hg::literal_wnaf_flatten 7 tg) 0,
   fold_left secp_wnaf15_digit_fold (hh::literal_wnaf_flatten 7 th) 0)).
Proof.
 pose proof (secp_strauss_four_maps (literal_wnaf5_flatten 7 t1) (literal_wnaf5_flatten 7 tl)
  (literal_wnaf_flatten 7 tg) (literal_wnaf_flatten 7 th)
  ltac:(rewrite !secp_wnaf5_flatten_length;reflexivity)
  ltac:(rewrite !literal_wnaf_flatten_length;reflexivity)
  ltac:(rewrite secp_wnaf5_flatten_length,literal_wnaf_flatten_length;reflexivity)) as Maps.
 cbn zeta in Maps;destruct Maps as [L1 [L2 [L3 L4]]].
 rewrite secp_strauss_coefficient_projected;cbn [map fst snd];apply f_equal2.
 - apply f_equal2.
   + exact (f_equal (fun xs=>fold_left secp_wnaf5_digit_fold (h1::xs) 0) L1).
   + exact (f_equal (fun xs=>fold_left secp_wnaf5_digit_fold (hl::xs) 0) L2).
 - apply f_equal2.
   + exact (f_equal (fun xs=>fold_left secp_wnaf15_digit_fold (hg::xs) 0) L3).
   + exact (f_equal (fun xs=>fold_left secp_wnaf15_digit_fold (hh::xs) 0) L4).
Qed.
Theorem secp_strauss_window_coefficients (s1 sl:Ty.tySem literal_wnaf_state)
 (gl gh:Ty.tySem (Word 7)):
 let w1:=@literal_wnaf5 Alg.CoreFunSem s1 in
 let wl:=@literal_wnaf5 Alg.CoreFunSem sl in
 let wg:=@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gl) in
 let wh:=@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gh) in
 fold_left secp_strauss_coefficient_step
  (((fst w1,fst wl),(fst wg,fst wh))::
   combine (combine (literal_wnaf5_flatten 7 (snd w1)) (literal_wnaf5_flatten 7 (snd wl)))
    (combine (literal_wnaf_flatten 7 (snd wg)) (literal_wnaf_flatten 7 (snd wh)))) ((0,0),(0,0))=
 ((secp_wnaf5_state_value s1,secp_wnaf5_state_value sl),(@toZ (WordToZ 7) gl,@toZ (WordToZ 7) gh)).
Proof.
 cbn zeta.
 destruct (@literal_wnaf5 Alg.CoreFunSem s1) as [h1 t1] eqn:W1.
 destruct (@literal_wnaf5 Alg.CoreFunSem sl) as [hl tl] eqn:WL.
 destruct (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gl)) as [hg tg] eqn:WG.
 destruct (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gh)) as [hh th] eqn:WH.
 cbn [fst snd];rewrite secp_strauss_merged_coefficients.
 pose proof (secp_wnaf5_digits_reconstruct s1) as V1.
 pose proof (secp_wnaf5_digits_reconstruct sl) as VL.
 pose proof (secp_wnaf15_digits_reconstruct gl) as VG.
 pose proof (secp_wnaf15_digits_reconstruct gh) as VH.
 unfold literal_wnaf5_digits in V1,VL;unfold literal_wnaf15_digits in VG,VH.
 rewrite W1 in V1;rewrite WL in VL;rewrite WG in VG;rewrite WH in VH.
 apply f_equal2;apply f_equal2;[exact V1|exact VL|exact VG|exact VH].
Qed.
From Coqprime.elliptic Require Import GZnZ.
Require Import C.jet_secp_curve_group C.jet_secp_curve_group_sign C.jet_secp_field_word_group
 C.jet_secp_jacobian_word_group C.jet_secp_table_pass2_group C.jet_secp_lookup5_group
 C.jet_secp_strauss_group C.jet_secp_literal_infinity C.jet_secp_fe_math C.jet_secp_wnaf_literal_values.
Theorem secp_literal_strauss_window_group (z:Ty.tySem (Word 8))
 (table:Ty.tySem (C.jet_secp_scalar_table_literal.literal_table_vector 3)) (p:secp_group_point)
 (s1 sl:Ty.tySem literal_wnaf_state) (gl gh:Ty.tySem (Word 7)):
 secp_field_word z<>GZnZ.zero feP ->
 secp_table_vector_group 3 table (secp_group_odd_table p) (secp_field_word z) ->
 secp_jacobian_word_rep (secp_field_word z)
 (@literal_strauss_digits129 Alg.CoreFunSem
  (@literal_gej_infinity Alg.CoreFunSem tt,((z,table),
   ((@literal_wnaf5 Alg.CoreFunSem s1,@literal_wnaf5 Alg.CoreFunSem sl),
    (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gl),@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gh))))))
 (secp_strauss_combination p
  ((secp_wnaf5_state_value s1,secp_wnaf5_state_value sl),(@toZ (WordToZ 7) gl,@toZ (WordToZ 7) gh))).
Proof.
 intros Nonzero Table.
 pose proof (secp_strauss_window_coefficients s1 sl gl gh) as Values.
 pose proof (literal_wnaf15_values gl) as GoodG;pose proof (literal_wnaf15_values gh) as GoodH.
 cbn zeta in Values.
 destruct (@literal_wnaf5 Alg.CoreFunSem s1) as [h1 t1] eqn:W1.
 destruct (@literal_wnaf5 Alg.CoreFunSem sl) as [hl tl] eqn:WL.
 destruct (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gl)) as [hg tg] eqn:WG.
 destruct (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gh)) as [hh th] eqn:WH.
 cbn [fst snd] in Values.
 assert (ValidG:Forall wnaf_literal_valid (hg::literal_wnaf_flatten 7 tg)).
 { exact (eq_ind (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gl))
   (fun result:Ty.tySem (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))=>
    Forall wnaf_literal_valid (let '(top,rest):=result in top::literal_wnaf_flatten 7 rest)) GoodG (hg,tg) WG). }
 assert (ValidH:Forall wnaf_literal_valid (hh::literal_wnaf_flatten 7 th)).
 { exact (eq_ind (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,gh))
   (fun result:Ty.tySem (Ty.Prod literal_wnaf_digit (Vector literal_wnaf_digit 7))=>
    Forall wnaf_literal_valid (let '(top,rest):=result in top::literal_wnaf_flatten 7 rest)) GoodH (hh,th) WH). }
 rewrite <-Values,literal_strauss_digits129_list.
 apply secp_literal_strauss_fold_scalar;[exact Nonzero|exact Table|].
 constructor.
 - split;[exact (Forall_inv ValidG)|exact (Forall_inv ValidH)].
 - apply secp_strauss_combined_valid;[exact (Forall_inv_tail ValidG)|exact (Forall_inv_tail ValidH)].
Qed.
