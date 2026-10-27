(** Compose all six remaining original scalar_split_lambda calls. Every
    intermediate execution, scalar value and bound is derived from storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support
 C.jet_secp_scalar_constant C.jet_secp_scalar_lambda_global C.jet_secp_split_multipliers
 C.jet_secp_split_constants C.jet_secp_split_rounding_calls C.jet_secp_split_arithmetic_calls
 C.jet_secp_scalar_inplace_values C.jet_secp_scalar_add_separate C.jet_secp_scalar_mul_separate
 C.jet_secp_scalar_borrowed_inputs C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge split_basis_block scalar_lambda_block.

Definition split_arithmetic_frame bk br1 br2 bc1 bc2 b (_:Z) :=
 b<>bk /\ b<>br1 /\ b<>br2 /\ b<>bc1 /\ b<>bc2 /\
 b<>split_basis_block true /\ b<>split_basis_block false /\ b<>scalar_lambda_block.

Theorem exec_split_arithmetic k le m bk br1 br2 bc1 bc2 :
 0<=k<canonical_group_order -> split_constants_ready m ->
 le!_k=Some (Vptr bk Ptrofs.zero) -> le!_r1=Some (Vptr br1 Ptrofs.zero) -> le!_r2=Some (Vptr br2 Ptrofs.zero) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of k)) ->
 scalar_at m bc1 0 (map Int64.repr (scalar_limbs_of (split_coefficient true k))) ->
 scalar_at m bc2 0 (map Int64.repr (scalar_limbs_of (split_coefficient false k))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m br1 0 32 Cur Freeable ->
 Mem.range_perm m br2 0 32 Cur Freeable -> Mem.range_perm m bc1 0 32 Cur Freeable ->
 Mem.range_perm m bc2 0 32 Cur Freeable -> NoDup [bk;br1;br2;bc1;bc2] ->
 exists mf,Clight2.exec_stmt secp_ge (split_local_env bc1 bc2) le m split_arithmetic_suffix E0 le mf Out_normal /\
 scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of (split_first_value k))) /\
 scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of (split_second_value k))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of k)) /\
 Mem.range_perm mf bc1 0 32 Cur Freeable /\ Mem.range_perm mf bc2 0 32 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ split_constants_ready mf /\
 lframe (split_arithmetic_frame bk br1 br2 bc1 bc2) m mf.
Proof.
 intros K Ready TK R1 R2 Input C1 C2 FK FR1 FR2 FC1 FC2 Distinct.
 assert (Sep:bk<>br1 /\ bk<>br2 /\ bk<>bc1 /\ bk<>bc2 /\ br1<>br2 /\
  br1<>bc1 /\ br1<>bc2 /\ br2<>bc1 /\ br2<>bc2 /\ bc1<>bc2).
 { repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence. }
 destruct Sep as (K1 & K2 & KC1 & KC2 & R12 & R1C1 & R1C2 & R2C1 & R2C2 & C12).
 destruct canonical_group_order_range as [[Npos Nsize] _];change (canonical_group_order<2^256) in Nsize.
 assert (K256:0<=k<2^256) by lia.
 pose proof (split_coefficient_bounds true k K256) as CB1.
 pose proof (split_coefficient_bounds false k K256) as CB2.
 pose proof (split_basis_bounds true) as B1;pose proof (split_basis_bounds false) as B2.
 destruct (eval_scalar_mul_inplace_values (split_coefficient true k) (split_basis_value true) m bc1
  (split_basis_block true) ltac:(lia) ltac:(lia) (split_basis_separate true m bc1 Ready FC1)
  C1 (split_basis_storage true m Ready) FC1)
  as (m1 & Call1 & Product1 & FC11 & Keep1 & Preserve1 & Frame1).
 change (scalar_at m1 bc1 0 (map Int64.repr (scalar_limbs_of (split_product true k)))) in Product1.
 assert (Ready1:split_constants_ready m1) by (eapply split_constants_readonly;[exact Ready|exact Preserve1]).
 assert (C21:scalar_at m1 bc2 0 (map Int64.repr (scalar_limbs_of (split_coefficient false k))))
  by (eapply scalar_at_lframe;[exact C2|exact Frame1|];intros;split;
      [congruence|exact (split_basis_separate true m bc2 Ready FC2)]).
 assert (FK1:Mem.range_perm m1 bk 0 32 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep1|exact FK]).
 assert (FC21:Mem.range_perm m1 bc2 0 32 Cur Freeable) by (eapply keeps_range_permissions;[exact Keep1|exact FC2]).
 assert (Input1:scalar_at m1 bk 0 (map Int64.repr (scalar_limbs_of k)))
  by (eapply scalar_at_lframe;[exact Input|exact Frame1|];intros;split;
      [exact KC1|exact (split_basis_separate true m bk Ready FK)]).
 destruct (eval_scalar_mul_inplace_values (split_coefficient false k) (split_basis_value false) m1 bc2
  (split_basis_block false) ltac:(lia) ltac:(lia) (split_basis_separate false m1 bc2 Ready1 FC21)
  C21 (split_basis_storage false m1 Ready1) FC21)
  as (m2 & Call2 & Product2 & FC22 & Keep2 & Preserve2 & Frame2).
 change (scalar_at m2 bc2 0 (map Int64.repr (scalar_limbs_of (split_product false k)))) in Product2.
 assert (Keep02:keeps_permissions m m2) by (eapply keeps_permissions_trans;[exact Keep1|exact Keep2]).
 assert (Ready2:split_constants_ready m2) by (eapply split_constants_readonly;[exact Ready1|exact Preserve2]).
 assert (Product12:scalar_at m2 bc1 0 (map Int64.repr (scalar_limbs_of (split_product true k))))
  by (eapply scalar_at_lframe;[exact Product1|exact Frame2|];intros;split;
      [exact C12|exact (split_basis_separate false m1 bc1 Ready1 FC11)]).
 assert (Input2:scalar_at m2 bk 0 (map Int64.repr (scalar_limbs_of k)))
  by (eapply scalar_at_lframe;[exact Input1|exact Frame2|];intros;split;
      [exact KC2|exact (split_basis_separate false m1 bk Ready1 FK1)]).
 destruct (eval_scalar_add_separate_values (split_product true k) (split_product false k) m2 br2 bc1 bc2
  (split_product_bounds true k) (split_product_bounds false k) R2C1 R2C2 C12 Product12 Product2
  ltac:(eapply keeps_range_permissions;[exact Keep02|exact FR2])
  ltac:(eapply keeps_range_permissions;[exact Keep02|exact FC1]) FC22)
  as (m3 & Call3 & Second & Product13 & Product23 & FR23 & FC13 & FC23 & Keep3 & Preserve3 & Frame3).
 change (scalar_at m3 br2 0 (map Int64.repr (scalar_limbs_of (split_second_value k)))) in Second.
 assert (Keep03:keeps_permissions m m3) by (eapply keeps_permissions_trans;[exact Keep02|exact Keep3]).
 assert (Ready3:split_constants_ready m3) by (eapply split_constants_readonly;[exact Ready2|exact Preserve3]).
 assert (Input3:scalar_at m3 bk 0 (map Int64.repr (scalar_limbs_of k)))
  by (eapply scalar_at_lframe;[exact Input2|exact Frame3|];intros;repeat split;assumption).
 pose proof (split_lambda_bounds) as LB.
 destruct (eval_scalar_mul_separate_values (split_second_value k) canonical_lambda_value m3 br1 br2 scalar_lambda_block
  ltac:(pose proof (split_second_bounds k);lia) ltac:(lia) R12
  (split_lambda_separate m3 br1 Ready3 ltac:(eapply keeps_range_permissions;[exact Keep03|exact FR1]))
  (split_lambda_separate m3 br2 Ready3 FR23) Second (split_lambda_storage m3 Ready3) FR23
  ltac:(eapply keeps_range_permissions;[exact Keep03|exact FR1]))
  as (m4 & Call4 & Lambda & SecondRep & FR14 & Keep4 & Preserve4 & Frame4).
 change (scalar_at m4 br1 0 (map Int64.repr (scalar_limbs_of (split_lambda_product k)))) in Lambda.
 destruct (scalar_borrowed_inputs_source (split_second_value k) canonical_lambda_value m4 br2 scalar_lambda_block SecondRep)
  as [Second4 FR24].
 assert (Keep04:keeps_permissions m m4) by (eapply keeps_permissions_trans;[exact Keep03|exact Keep4]).
 assert (Input4:scalar_at m4 bk 0 (map Int64.repr (scalar_limbs_of k)))
  by (eapply scalar_at_lframe;[exact Input3|exact Frame4|];intros;repeat split;
      [exact K1|exact K2|exact (split_lambda_separate m3 bk Ready3
        ltac:(eapply keeps_range_permissions;[exact Keep03|exact FK]))]).
 destruct (eval_scalar_negate_value (split_lambda_product k) m4 br1 (split_lambda_product_bounds k) Lambda FR14)
  as (m5 & Call5 & Negated & FR15 & Keep5 & Preserve5 & Frame5).
 change (scalar_at m5 br1 0 (map Int64.repr (scalar_limbs_of (split_negated_value k)))) in Negated.
 assert (Keep05:keeps_permissions m m5) by (eapply keeps_permissions_trans;[exact Keep04|exact Keep5]).
 assert (Input5:scalar_at m5 bk 0 (map Int64.repr (scalar_limbs_of k)))
  by (eapply scalar_at_lframe;[exact Input4|exact Frame5|];intros;exact K1).
 assert (Second5:scalar_at m5 br2 0 (map Int64.repr (scalar_limbs_of (split_second_value k))))
  by (eapply scalar_at_lframe;[exact Second4|exact Frame5|];intros;congruence).
 destruct (eval_scalar_add_inplace_values (split_negated_value k) k m5 br1 bk (split_negated_bounds k) K
  ltac:(congruence) Negated Input5 FR15 ltac:(eapply keeps_range_permissions;[exact Keep05|exact FK]))
  as (mf & Call6 & First & InputF & FR1F & FKF & Keep6 & Preserve6 & Frame6).
 change (scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of (split_first_value k)))) in First.
 assert (SecondF:scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of (split_second_value k))))
  by (eapply scalar_at_lframe;[exact Second5|exact Frame6|];intros;split;congruence).
 assert (Keep:keeps_permissions m mf) by (eapply keeps_permissions_trans;[exact Keep05|exact Keep6]).
 assert (Preserve:readonly_preserved m mf).
 { eapply preserved_trans;[exact Preserve1|];eapply preserved_trans;[exact Preserve2|];
   eapply preserved_trans;[exact Preserve3|];eapply preserved_trans;[exact Preserve4|];
   eapply preserved_trans;[exact Preserve5|exact Preserve6]. }
 exists mf;split.
 - rewrite split_arithmetic_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le);
    [apply exec_split_product;exact Call1|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le);
    [apply exec_split_product;exact Call2|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le);
    [eapply exec_split_second;[exact R2|exact Call3]|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m4) (le1:=le);
    [eapply exec_split_lambda;[exact R1|exact R2|exact Call4]|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m5) (le1:=le);
    [eapply exec_split_negate;[exact R1|exact Call5]|].
   eapply exec_split_last;[exact R1|exact TK|exact Call6].
 - split;[exact First|];split;[exact SecondF|];split;[exact InputF|];split;
   [eapply keeps_range_permissions;[exact Keep|exact FC1]|];split;
   [eapply keeps_range_permissions;[exact Keep|exact FC2]|];split;[exact Keep|];split;
   [exact Preserve|];split;[eapply split_constants_readonly;[exact Ready|exact Preserve]|].
   eapply lframe_trans with (m2:=m1).
   + eapply lframe_implies;[exact Frame1|];unfold split_arithmetic_frame;intros;tauto.
   + eapply lframe_trans with (m2:=m2).
     * eapply lframe_implies;[exact Frame2|];unfold split_arithmetic_frame;intros;tauto.
     * eapply lframe_trans with (m2:=m3).
       -- eapply lframe_implies;[exact Frame3|];unfold split_arithmetic_frame;intros;tauto.
       -- eapply lframe_trans with (m2:=m4).
          ++ eapply lframe_implies;[exact Frame4|];unfold split_arithmetic_frame;intros;tauto.
          ++ eapply lframe_trans with (m2:=m5).
             ** eapply lframe_implies;[exact Frame5|];unfold split_arithmetic_frame;intros;tauto.
             ** eapply lframe_implies;[exact Frame6|];unfold split_arithmetic_frame;intros;tauto.
Qed.
