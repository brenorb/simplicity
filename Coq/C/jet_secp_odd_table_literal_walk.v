(** Couple the checked C limb recurrence to the exact literal additions.
    Intermediate bounds are obtained from actual C iterations, not assumed
    as a trace-wide arithmetic premise. Raw literal ratios are related by
    field residue, as required by their subsequent multiplication consumers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_scalar_table_literal C.jet_secp_odd_table_loop C.jet_secp_odd_table_iteration
 C.jet_secp_mixed_xy_ratio_literal C.jet_secp_mixed_xy_flag C.jet_secp_mixed_body_loose
 C.jet_secp_mixed_body_ratio_slice C.jet_secp_square_columns C.jet_secp_field_zero_owned
 C.jet_secp_rescale_literal C.jet_secp_canonical_normalize C.jet_secp_canonical_zero
 C.jet_secp_curve_statements C.jet_secp_add_literal.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_ge_add_ex rescale_field_output canonical_fe_normalize.

Definition table_word_literal w (a:Ty.tySem (Word 8)) :=
 radix_value w mod feP=@toZ (WordToZ 8) a mod feP.
Definition table_acc_literal s (a:Ty.tySem literal_table_gej) :=
 table_word_literal (odd_table_x s) (fst (fst a)) /\
 table_word_literal (odd_table_y s) (snd (fst a)) /\
 table_word_literal (odd_table_z s) (snd a) /\ odd_table_flag s=field_zero_result (odd_table_z s).
Definition table_prefix_literal n s a b := forall j,(j<n)%nat ->
 table_word_literal (odd_table_xs s j) (fst (fst (literal_table_advance j a b))) /\
 table_word_literal (odd_table_ys s j) (snd (fst (literal_table_advance j a b))) /\
 ((0<j)%nat -> table_word_literal (odd_table_ratios s j) (literal_table_ratio (Nat.pred j) a b)).

Lemma table_decoded_literal w a : rescale_field_output w=a -> table_word_literal w a.
Proof.
 intro Equal;pose proof (f_equal (fun v=>@toZ (WordToZ 8) v) Equal) as Value.
 rewrite rescale_field_output_value,field_prime_matches_normalizer in Value.
 unfold table_word_literal;rewrite <-Value,Z.mod_mod by (unfold feP,feR;lia);reflexivity.
Qed.
Lemma table_normalized_literal w a : table_word_literal w (@canonical_fe_normalize Alg.CoreFunSem a) ->
 table_word_literal w a.
Proof.
 unfold table_word_literal;rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model,
  Z.mod_mod by (unfold feP,feR;lia);trivial.
Qed.

Theorem odd_table_next_literal j s u v a b :
 odd_table_accumulator_bounds s -> square_input_bounds u -> square_input_bounds v ->
 table_acc_literal s a -> table_word_literal u (fst b) -> table_word_literal v (snd b) ->
 table_acc_literal (odd_table_next s u v j) (snd (@literal_gej_ge_add_ex Alg.CoreFunSem (a,b))) /\
 table_word_literal (odd_table_ratios (odd_table_next s u v j) j) (fst (@literal_gej_ge_add_ex Alg.CoreFunSem (a,b))).
Proof.
 intros (BX & BY & BZ) BU BV (HX & HY & HZ & Flag) HU HV.
 destruct a as [[ax ay] az];destruct b as [bx byword].
 pose proof (mixed_xy_ex_outputs_literal (odd_table_x s) (odd_table_y s) (odd_table_z s) u v
   ax ay az bx byword BX BY BZ BU BV HX HY HZ HU HV) as Literal.
 cbv zeta in Literal;rewrite <- (mixed_flag_of_residue _ az HZ),<-Flag in Literal.
 pose proof (f_equal (fun r=>fst r) Literal) as LR.
 pose proof (f_equal (fun r=>fst (fst (snd r))) Literal) as LX.
 pose proof (f_equal (fun r=>snd (fst (snd r))) Literal) as LY.
 pose proof (f_equal (fun r=>snd (snd r)) Literal) as LZ.
 cbn [fst snd] in LR,LX,LY,LZ.
 split.
 - split;[apply table_decoded_literal;exact LX|];split;[apply table_decoded_literal;exact LY|];
    split;[apply table_decoded_literal;exact LZ|].
   exact (mixed_xy_flag_preserved _ _ _ _ _ _ BX BY BZ BU BV Flag).
 - cbn [odd_table_next odd_table_ratios];unfold odd_table_replace;destruct (Nat.eq_dec j j);[|contradiction].
   apply table_normalized_literal;apply table_decoded_literal;exact LR.
Qed.

Lemma table_prefix_literal_next j s u v a b :
 table_prefix_literal j s a b ->
 table_acc_literal (odd_table_next s u v j) (literal_table_advance j a b) ->
 table_word_literal (odd_table_ratios (odd_table_next s u v j) j) (literal_table_ratio (Nat.pred j) a b) ->
 table_prefix_literal (S j) (odd_table_next s u v j) a b.
Proof.
 intros Prefix (X & Y & Z & Flag) Ratio k Bound.
 unfold odd_table_next;cbn [odd_table_xs odd_table_ys odd_table_ratios];unfold odd_table_replace.
 destruct (Nat.eq_dec k j) as [->|Different].
 - split;[exact X|];split;[exact Y|];intro Positive.
   cbn [odd_table_next odd_table_ratios] in Ratio;unfold odd_table_replace in Ratio;
    destruct (Nat.eq_dec j j);[exact Ratio|contradiction].
 - exact (Prefix k ltac:(lia)).
Qed.

Theorem odd_table_walk_literal n : forall j,(1<=j)%nat -> (j+n<=8)%nat ->
 forall e le m br ba bg bz s u v a b,
 NoDup [br;ba;bg;bz] -> e!_ai=Some (ba,Tstruct __6123 noattr) -> e!_d_ge=Some (bg,curve_ge_type) ->
 e!_secp256k1_gej_add_ge_var=None -> e!_secp256k1_ge_set_xy=None ->
 le!_pre_a=Some (Vptr br Ptrofs.zero) -> le!_zr=Some (Vptr bz Ptrofs.zero) ->
 le!_i=Some (Vint (Int.repr (Z.of_nat j))) ->
 odd_table_accumulator m ba s -> odd_table_accumulator_bounds s ->
 square_input_bounds u -> square_input_bounds v ->
 fe_at m bg 0 (words5 u) -> fe_at m bg 40 (words5 v) -> Mem.load Mint32 m bg 80=Some (Vint Int.zero) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bg 0 88 Cur Freeable -> Mem.range_perm m bz 0 320 Cur Freeable ->
 table_acc_literal s (literal_table_advance (Nat.pred j) a b) -> table_prefix_literal j s a b ->
 table_word_literal u (fst b) -> table_word_literal v (snd b) ->
 let sf:=odd_table_walk n j s u v in
 table_acc_literal sf (literal_table_advance (Nat.pred (j+n)) a b) /\ table_prefix_literal (j+n) sf a b.
Proof.
 induction n as [|n IH];intros j Start Limit e le m br ba bg bz s u v a b Distinct AI DG AddGlobal WriteGlobal
  Table Ratios IndexTemp Acc Bounds BU BV U V Flag FreeT FreeA FreeG FreeR AccLiteral PrefixLiteral UL VL.
 - cbn [odd_table_walk];rewrite Nat.add_0_r;split;assumption.
 - destruct j as [|k];[lia|].
   assert (Index:1<=Z.of_nat (S k)<8) by lia.
   destruct Acc as (X & Y & Z & AFlag);destruct Bounds as (BX & BY & BZ).
   destruct (exec_odd_table_iteration e le (odd_table_x s) (odd_table_y s) (odd_table_z s) u v (odd_table_flag s)
     m br ba bg bz (Z.of_nat (S k)) Index Distinct AI DG AddGlobal WriteGlobal Table Ratios IndexTemp
     BX BY BZ BU BV X Y Z AFlag U V Flag FreeT FreeA FreeG FreeR)
    as (m1 & Iteration & X1 & Y1 & Z1 & Flag1 & U1 & V1 & GFlag1 & TX & TY & TFlag & Ratio1 &
      BX1 & BY1 & BZ1 & RatioBound & FreeT1 & FreeA1 & FreeG1 & FreeR1 & Keep1 & Frame1 & Readonly1).
   assert (Bounds0:odd_table_accumulator_bounds s) by (split;[exact BX|];split;assumption).
   destruct (odd_table_next_literal (S k) s u v (literal_table_advance k a b) b
     Bounds0 BU BV AccLiteral UL VL) as [NextAcc NextRatio].
   set (s1:=odd_table_next s u v (S k)).
   assert (NextAccLiteral:table_acc_literal s1 (literal_table_advance (S k) a b)) by exact NextAcc.
   assert (NextPrefixLiteral:table_prefix_literal (S (S k)) s1 a b).
   { apply table_prefix_literal_next;[exact PrefixLiteral|exact NextAccLiteral|exact NextRatio]. }
   assert (NextMemory:odd_table_accumulator m1 ba s1) by
    (split;[exact X1|];split;[exact Y1|];split;[exact Z1|exact Flag1]).
   assert (NextBounds:odd_table_accumulator_bounds s1) by (split;[exact BX1|];split;assumption).
   set (le1:=odd_table_iteration_temps le (Z.of_nat (S k))).
   assert (Other:forall id,id<>_i -> le1!id=le!id) by
    (intros id Different;unfold le1,odd_table_iteration_temps;apply PTree.gso;exact Different).
   pose proof (IH (S (S k)) ltac:(lia) ltac:(lia) e le1 m1 br ba bg bz s1 u v a b Distinct AI DG AddGlobal WriteGlobal
     ltac:(rewrite Other by discriminate;exact Table) ltac:(rewrite Other by discriminate;exact Ratios)
     ltac:(unfold le1,odd_table_iteration_temps;rewrite PTree.gss;
       replace (Z.of_nat (S (S k))) with (Z.of_nat (S k)+1) by (clear -k;lia);reflexivity)
     NextMemory NextBounds BU BV U1 V1 GFlag1 FreeT1 FreeA1 FreeG1 FreeR1 NextAccLiteral NextPrefixLiteral UL VL)
    as Result.
   cbn [odd_table_walk];replace (S k+S n)%nat with (S (S k)+n)%nat by lia;exact Result.
Qed.
