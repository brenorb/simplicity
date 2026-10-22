(** Actual candidate computation, checking square, equality and return suffix. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_field_pair_multiply C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_statement_prefix C.jet_secp_root_square_loop C.jet_secp_root_stage C.jet_secp_root_chain_owned
 C.jet_secp_root_chain_numeric C.jet_secp_root_call_state C.jet_secp_root_prefix
 C.jet_secp_root_candidate_state C.jet_secp_root_check.
Require Import C.jet_secp_root_suffix C.jet_secp_root_affine_y_state.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words field_pair_product root_chain_candidate.


Definition root_y_suffix_frame e ba br b pos :=
 root_chain_frame e b pos /\ b<>ba /\ (b<>br \/ pos<40 \/ 80<=pos).
Local Ltac keep_root_field FieldHyp FrameHyp :=
 eapply curve_keep_field_range;[reflexivity|exact FieldHyp|exact FrameHyp|];intros;repeat split;first [congruence|left;congruence].
Local Ltac keep_root_free FreeHyp FrameHyp :=
 eapply curve_keep_free;[lia|exact FreeHyp|exact FrameHyp|];intros;repeat split;first [congruence|left;congruence].
Local Ltac root_suffix_frame_from F IT ET I2 E2 :=
 eapply lframe_implies;[exact F|];intros bx pos [HO [NA NR]] _;
 repeat split;first [exact NA|exact NR|intro HE;subst bx;
   first [exact (HO _ IT ET)|exact (HO _ I2 E2)]].

Theorem exec_root_candidate_suffix_affine_y e le m ba br w (x : Ty.tySem (Word 8)) :
 root_locals_separated e -> root_locals_owned e m ->
 root_values_at e m (root_chain_final (root_initial_x2 w) (root_initial_x3 w)) ->
 root_chain_frame e ba 0 -> root_chain_frame e br 0 -> ba<>br ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_equal_var=None ->
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr br (Ptrofs.repr 40)) ->
 root_words_match w x -> fe_at m ba 0 (words5 w) ->
 Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable -> exists mf lef,
 Clight2.exec_stmt secp_ge e le m root_after_chain E0 lef mf
   (Out_return (Some (Vint (if root_check_flag w then Int.one else Int.zero),tint))) /\
 root_locals_owned e mf /\ fe_at mf br 40 (words5 (root_chain_candidate w)) /\
 Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (root_y_suffix_frame e ba br) m mf.
Proof.
 intros Sep Owned Store OutsideA OutsideR AR EQ EM EE HA HR Match A FA FR.
 assert (IT : In _t1 root_private_ids) by (unfold root_private_ids;repeat (first [left;reflexivity|right])).
 assert (I2 : In _x2 root_private_ids) by (left;reflexivity).
 destruct (Owned _t1 IT) as (bt & ET & FT);destruct (Owned _x2 I2) as (b2 & E2 & F2).
 assert (TA : bt<>ba) by (intro HE;subst bt;exact (OutsideA _t1 IT ET)).
 assert (TR : bt<>br) by (intro HE;subst bt;exact (OutsideR _t1 IT ET)).
 assert (A2 : b2<>ba) by (intro HE;subst b2;exact (OutsideA _x2 I2 E2)).
 assert (R2 : b2<>br) by (intro HE;subst b2;exact (OutsideR _x2 I2 E2)).
 assert (T2 : bt<>b2) by (exact (Sep _t1 _x2 bt b2 IT I2 ET E2 ltac:(discriminate))).
 assert (LT : (root_chain_final (root_initial_x2 w) (root_initial_x3 w))!_t1=Some (snd (root_chain_window w)))
   by (exact (root_chain_final_t1 w)).
 assert (L2 : (root_chain_final (root_initial_x2 w) (root_initial_x3 w))!_x2=Some (fst (root_chain_window w)))
   by (exact (root_chain_final_x2 (root_initial_x2 w) (root_initial_x3 w))).
 destruct (exec_root_squares_state 6 e le m _ _t1 bt (snd (root_chain_window w))
   ltac:(lia) Sep Owned Store LT ET EQ) as (m1 & le1 & C1 & Owned1 & Store1 & Temps & Frame1).
 destruct (Store1 _x2 (fst (root_chain_window w)) ltac:(rewrite PTree.gso by discriminate;exact L2))
   as (_ & BX2 & b2' & E2' & X2);rewrite E2 in E2';injection E2' as <-.
 destruct (Owned1 _x2 I2) as (b2' & E2' & F21);rewrite E2 in E2';injection E2' as <-.
 destruct (exec_root_multiply_state e le1 m1 _ _t1 bt b2 (curve_local_address _x2)
   (root_square_words 6 (snd (root_chain_window w))) (fst (root_chain_window w))
   Sep Owned1 Store1 IT ET EM eq_refl ltac:(apply eval_curve_local;exact E2) T2 (PTree.gss _ _ _) BX2 X2 F21)
   as (m2 & C2 & Owned2 & Store2 & X2F & F2F & Frame2).
 destruct (exec_root_inplace_square_state e le1 m2 _ _t1 bt _ Sep Owned2 Store2 (PTree.gss _ _ _) ET EQ)
   as (m3 & C3 & Owned3 & Store3 & Frame3).
 assert (HR1 : le1!_r=Some (Vptr br (Ptrofs.repr 40))) by (rewrite Temps by discriminate;exact HR).
 assert (HA1 : le1!_a=Some (Vptr ba Ptrofs.zero)) by (rewrite Temps by discriminate;exact HA).
 assert (FR1 : Mem.range_perm m1 br 0 88 Cur Freeable) by (keep_root_free FR Frame1).
 assert (FR2 : Mem.range_perm m2 br 0 88 Cur Freeable) by (keep_root_free FR1 Frame2).
 assert (FR3 : Mem.range_perm m3 br 0 88 Cur Freeable) by (keep_root_free FR2 Frame3).
 destruct (exec_root_square_out_affine_y_state e le1 m3 _ _t1 bt br root_result_argument _
   Owned3 Store3 (PTree.gss _ _ _) ET OutsideR EQ eq_refl ltac:(apply eval_Etempvar;exact HR1) FR3)
   as (m4 & C4 & Owned4 & Store4 & R4 & FR4 & Frame4).
 change (fe_at m4 br 40 (words5 (root_chain_candidate w))) in R4.
 pose proof (root_chain_candidate_matches w x Match) as [BR VR].
 destruct (exec_root_square_from_affine_y_state e le1 m4 _ _t1 bt br root_result_argument (root_chain_candidate w)
   Sep Owned4 Store4 IT ET OutsideR EQ eq_refl ltac:(apply eval_Etempvar;exact HR1) BR R4 FR4)
   as (m5 & C5 & Owned5 & Store5 & R5 & FR5 & Frame5).
 destruct (Store5 _t1 (square_words (root_chain_candidate w)) (PTree.gss _ _ _))
   as (_ & BCheck & bt' & ET' & Check);rewrite ET in ET';injection ET' as <-.
 destruct (Owned5 _t1 IT) as (bt' & ET' & FT5);rewrite ET in ET';injection ET' as <-.
 assert (A1 : fe_at m1 ba 0 (words5 w)) by (keep_root_field A Frame1).
 assert (A2F : fe_at m2 ba 0 (words5 w)) by (keep_root_field A1 Frame2).
 assert (A3 : fe_at m3 ba 0 (words5 w)) by (keep_root_field A2F Frame3).
 assert (A4 : fe_at m4 ba 0 (words5 w)) by (keep_root_field A3 Frame4).
 assert (A5 : fe_at m5 ba 0 (words5 w)) by (keep_root_field A4 Frame5).
 assert (FA1 : Mem.range_perm m1 ba 0 40 Cur Freeable) by (keep_root_free FA Frame1).
 assert (FA2 : Mem.range_perm m2 ba 0 40 Cur Freeable) by (keep_root_free FA1 Frame2).
 assert (FA3 : Mem.range_perm m3 ba 0 40 Cur Freeable) by (keep_root_free FA2 Frame3).
 assert (FA4 : Mem.range_perm m4 ba 0 40 Cur Freeable) by (keep_root_free FA3 Frame4).
 assert (FA5 : Mem.range_perm m5 ba 0 40 Cur Freeable) by (keep_root_free FA4 Frame5).
 destruct (exec_root_final_check e le1 m5 bt ba w x Match TA HA1 ET EE Check A5 FT5 FA5)
   as (mf & CheckRun & FTF & FAF & FrameF).
 assert (OwnedF : root_locals_owned e mf).
 { intros j HJ;destruct (Owned5 j HJ) as (b & EB & FB);exists b;split;[exact EB|].
   destruct (Pos.eq_dec b bt) as [->|NT];[exact FTF|].
   eapply curve_keep_free;[lia|exact FB|exact FrameF|];intros;split;[exact NT|].
   intro HE;subst b;exact (OutsideA j HJ EB). }
 assert (RF : fe_at mf br 40 (words5 (root_chain_candidate w))) by (keep_root_field R5 FrameF).
 assert (FRF : Mem.range_perm mf br 0 88 Cur Freeable) by (keep_root_free FR5 FrameF).
 assert (Frame : lframe (root_y_suffix_frame e ba br) m mf).
 { eapply lframe_trans;[root_suffix_frame_from Frame1 IT ET I2 E2|].
   eapply lframe_trans;[root_suffix_frame_from Frame2 IT ET I2 E2|].
   eapply lframe_trans;[root_suffix_frame_from Frame3 IT ET I2 E2|].
   eapply lframe_trans.
   - eapply lframe_implies;[exact Frame4|].
     intros bx pos [HO [NA NR]] _;split;[intro HE;subst bx;exact (HO _ IT ET)|exact NR].
   - eapply lframe_trans.
     + eapply lframe_implies;[exact Frame5|].
       intros bx pos [HO [NA NR]] _;split;[intro HE;subst bx;exact (HO _ IT ET)|exact NR].
     + root_suffix_frame_from FrameF IT ET I2 E2. }
 exists mf,(PTree.set _t'1 (Vint (if root_check_flag w then Int.one else Int.zero)) le1);split.
 - rewrite root_candidate_suffix_source;unfold root_candidate_statements;cbn [statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C1|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C2|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C3|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C4|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C5|exact CheckRun].
 - split;[exact OwnedF|];split;[exact RF|];split;[exact FAF|];split;assumption.
Qed.

Theorem exec_root_complete_body_affine_y e le m ba br w (x : Ty.tySem (Word 8)) :
 root_locals_separated e -> root_locals_owned e m ->
 root_chain_frame e ba 0 -> root_chain_frame e br 0 -> ba<>br ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_equal_var=None ->
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr br (Ptrofs.repr 40)) ->
 root_words_match w x -> fe_at m ba 0 (words5 w) ->
 Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable -> exists mf lef,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_fe_sqrt_var) E0 lef mf
   (Out_return (Some (Vint (if root_check_flag w then Int.one else Int.zero),tint))) /\
 root_locals_owned e mf /\ fe_at mf br 40 (words5 (root_chain_candidate w)) /\
 Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (root_y_suffix_frame e ba br) m mf.
Proof.
 intros Sep Owned OutsideA OutsideR AR EQ EM EE HA HR Match A FA FR.
 destruct (exec_root_chain_from_input e le m ba w Sep Owned OutsideA EQ EM HA (proj1 Match) A FA)
   as (mi & lei & Prefix & OwnedI & StoreI & AI & FAI & Temps & FrameI).
 assert (FRI : Mem.range_perm mi br 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FR|exact FrameI|];intros;split;[exact OutsideR|congruence]. }
 assert (HAI : lei!_a=Some (Vptr ba Ptrofs.zero)) by (rewrite Temps by discriminate;exact HA).
 assert (HRI : lei!_r=Some (Vptr br (Ptrofs.repr 40))) by (rewrite Temps by discriminate;exact HR).
 destruct (exec_root_candidate_suffix_affine_y e lei mi ba br w x Sep OwnedI StoreI OutsideA OutsideR AR
   EQ EM EE HAI HRI Match AI FAI FRI) as (mf & lef & Suffix & OwnedF & RF & FAF & FRF & FrameF).
 exists mf,lef;split.
 - rewrite root_input_prefix_source,<-root_precheck_sequence.
   apply exec_statement_prefix_then_last with (le1:=lei) (m1:=mi).
   + rewrite root_precheck_sequence;exact Prefix.
   + exact Suffix.
 - split;[exact OwnedF|];split;[exact RF|];split;[exact FAF|];split;[exact FRF|].
   eapply lframe_trans;[|exact FrameF].
   eapply lframe_implies;[exact FrameI|];intros b pos [HO [NA NR]] _;split;assumption.
Qed.
