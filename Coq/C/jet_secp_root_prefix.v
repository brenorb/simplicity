(** Actual assertion-disabled entry check and first four arithmetic calls.
    Establishes x2/x3 storage; no initialized private destination is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_root_chain_owned
 C.jet_secp_root_call_state C.jet_secp_field_pair_multiply C.jet_secp_statement_prefix.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words field_pair_product.

Definition root_argument := Etempvar _a (tptr curve_fe_type).
Definition root_initial_x2 w := field_pair_product (square_words w) w.
Definition root_initial_x3 w := field_pair_product (square_words (root_initial_x2 w)) w.
Definition root_prefix_calls last := Ssequence (root_square_stmt _x2 root_argument)
 (Ssequence (root_multiply_stmt _x2 root_argument)
 (Ssequence (root_square_stmt _x3 (curve_local_address _x2))
 (Ssequence (root_multiply_stmt _x3 root_argument) last))).
Definition root_prefix_frame e ba b pos := root_chain_frame e b pos /\ b<>ba.
Lemma root_prefix_source : fn_body f_secp256k1_fe_sqrt_var=
 Ssequence (Sloop Sskip Sbreak) (root_prefix_calls (root_drop_statements 5 (fn_body f_secp256k1_fe_sqrt_var))).
Proof. reflexivity. Qed.

Lemma root_prefix_initial_state w :
 PTree.set _x3 (root_initial_x3 w)
   (PTree.set _x3 (square_words (root_initial_x2 w))
     (PTree.set _x2 (root_initial_x2 w) (PTree.set _x2 (square_words w) (PTree.empty (nat -> int64)))))=
 root_chain_initial (root_initial_x2 w) (root_initial_x3 w).
Proof.
 rewrite !PTree.set2;apply PTree.extensionality;intro i;unfold root_chain_initial.
 destruct (Pos.eq_dec i _x2) as [->|N2];[rewrite !PTree.gso by discriminate;rewrite !PTree.gss;reflexivity|].
 destruct (Pos.eq_dec i _x3) as [->|N3].
 - rewrite PTree.gss,PTree.gso by discriminate;rewrite PTree.gss;reflexivity.
 - rewrite !PTree.gso by congruence;reflexivity.
Qed.

Lemma root_prefix_call_frame e ba bd bs m mf id :
 In id root_private_ids -> e!id=Some (bd,curve_fe_type) ->
 (bs=ba \/ exists j, In j root_private_ids /\ e!j=Some (bs,curve_fe_type)) ->
 lframe (fun b _=>b<>bd /\ b<>bs) m mf -> lframe (root_prefix_frame e ba) m mf.
Proof.
 intros ID ED Src Frame;eapply lframe_implies;[exact Frame|];intros b pos [HO HA] _;split.
 - intro HE;subst b;apply (HO id ID);exact ED.
 - destruct Src as [->|[j [IJ EJ]]];[exact HA|].
   intro HE;subst b;apply (HO j IJ);exact EJ.
Qed.

Theorem exec_root_prefix e le m ba w :
 root_locals_separated e -> root_locals_owned e m -> root_chain_frame e ba 0 ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> le!_a=Some (Vptr ba Ptrofs.zero) ->
 square_input_bounds w -> fe_at m ba 0 (words5 w) -> Mem.range_perm m ba 0 40 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m (Ssequence (Sloop Sskip Sbreak) (root_prefix_calls Sskip)) E0 le mf Out_normal /\
 root_locals_owned e mf /\ root_values_at e mf (root_chain_initial (root_initial_x2 w) (root_initial_x3 w)) /\
 fe_at mf ba 0 (words5 w) /\ Mem.range_perm mf ba 0 40 Cur Freeable /\
 lframe (root_prefix_frame e ba) m mf.
Proof.
 intros Sep Owned Outside EQ EM HA BW W FW.
 assert (I2 : In _x2 root_private_ids) by (left;reflexivity).
 assert (I3 : In _x3 root_private_ids) by (right;left;reflexivity).
 destruct (Owned _x2 I2) as (b2 & E2 & F2);destruct (Owned _x3 I3) as (b3 & E3 & F3).
 assert (N2 : b2<>ba) by (intro HE;subst b2;exact (Outside _x2 I2 E2)).
 assert (N3 : b3<>ba) by (intro HE;subst b3;exact (Outside _x3 I3 E3)).
 assert (N32 : b3<>b2) by (exact (Sep _x3 _x2 b3 b2 I3 I2 E3 E2 ltac:(discriminate))).
 assert (Empty : root_values_at e m (PTree.empty (nat -> int64))).
 { intros id u HU;rewrite PTree.gempty in HU;discriminate. }
 destruct (exec_root_square_state e le m _ _x2 b2 ba root_argument w
   Sep Owned Empty I2 E2 EQ eq_refl ltac:(apply eval_Etempvar;exact HA) N2 BW W FW)
   as (m1 & C1 & Owned1 & Store1 & W1 & FW1 & Frame1).
 destruct (exec_root_multiply_state e le m1 _ _x2 b2 ba root_argument (square_words w) w
   Sep Owned1 Store1 I2 E2 EM eq_refl ltac:(apply eval_Etempvar;exact HA) N2 (PTree.gss _ _ _) BW W1 FW1)
   as (m2 & C2 & Owned2 & Store2 & W2 & FW2 & Frame2).
 destruct (Store2 _x2 (root_initial_x2 w) (PTree.gss _ _ _)) as (_ & B2 & b2' & E2' & X2).
 rewrite E2 in E2';injection E2' as <-.
 destruct (Owned2 _x2 I2) as (b2' & E2' & F2');rewrite E2 in E2';injection E2' as <-.
 destruct (exec_root_square_state e le m2 _ _x3 b3 b2 (curve_local_address _x2) (root_initial_x2 w)
   Sep Owned2 Store2 I3 E3 EQ eq_refl ltac:(apply eval_curve_local;exact E2) N32 B2 X2 F2')
   as (m3 & C3 & Owned3 & Store3 & X2F & F2F & Frame3).
 assert (W3 : fe_at m3 ba 0 (words5 w)).
 { eapply curve_keep_field_range;[reflexivity|exact W2|exact Frame3|];intros;split;congruence. }
 assert (FW3 : Mem.range_perm m3 ba 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FW2|exact Frame3|];intros;split;congruence. }
 destruct (exec_root_multiply_state e le m3 _ _x3 b3 ba root_argument (square_words (root_initial_x2 w)) w
   Sep Owned3 Store3 I3 E3 EM eq_refl ltac:(apply eval_Etempvar;exact HA) N3 (PTree.gss _ _ _) BW W3 FW3)
   as (mf & C4 & OwnedF & StoreF & WF & FWF & Frame4).
 change (root_values_at e mf (PTree.set _x3 (root_initial_x3 w)
   (PTree.set _x3 (square_words (root_initial_x2 w))
     (PTree.set _x2 (root_initial_x2 w) (PTree.set _x2 (square_words w) (PTree.empty (nat -> int64))))))) in StoreF.
 rewrite root_prefix_initial_state in StoreF.
 assert (Frame : lframe (root_prefix_frame e ba) m mf).
 { eapply lframe_trans;[eapply root_prefix_call_frame;[exact I2|exact E2|left;reflexivity|exact Frame1]|].
   eapply lframe_trans;[eapply root_prefix_call_frame;[exact I2|exact E2|left;reflexivity|exact Frame2]|].
   eapply lframe_trans;[eapply root_prefix_call_frame;[exact I3|exact E3|right;exists _x2;split;[exact I2|exact E2]|exact Frame3]|].
   eapply root_prefix_call_frame;[exact I3|exact E3|left;reflexivity|exact Frame4]. }
 exists mf;split.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
   + eapply exec_Sloop_stop2 with (out1:=Out_normal) (out2:=Out_break) (t1:=E0) (t2:=E0);
       constructor.
   + unfold root_prefix_calls.
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C1|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C2|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C3|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact C4|constructor].
 - split;[exact OwnedF|];split;[exact StoreF|];split;[exact WF|];split;assumption.
Qed.

Definition root_start_statements := [Sloop Sskip Sbreak;
 root_square_stmt _x2 root_argument;root_multiply_stmt _x2 root_argument;
 root_square_stmt _x3 (curve_local_address _x2);root_multiply_stmt _x3 root_argument].
Lemma root_prefix_as_sequence last :
 statement_sequence root_start_statements last=Ssequence (Sloop Sskip Sbreak) (root_prefix_calls last).
Proof. reflexivity. Qed.
Lemma root_input_prefix_source : fn_body f_secp256k1_fe_sqrt_var=
 statement_sequence root_start_statements (root_chain_body root_chain_steps root_after_chain).
Proof. rewrite root_prefix_source,root_chain_body_source;reflexivity. Qed.

Theorem exec_root_chain_from_input e le m ba w :
 root_locals_separated e -> root_locals_owned e m -> root_chain_frame e ba 0 ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> le!_a=Some (Vptr ba Ptrofs.zero) ->
 square_input_bounds w -> fe_at m ba 0 (words5 w) -> Mem.range_perm m ba 0 40 Cur Freeable ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m
  (statement_sequence root_start_statements (root_chain_body root_chain_steps Sskip)) E0 lef mf Out_normal /\
 root_locals_owned e mf /\
 root_values_at e mf (root_chain_final (root_initial_x2 w) (root_initial_x3 w)) /\
 fe_at mf ba 0 (words5 w) /\ Mem.range_perm mf ba 0 40 Cur Freeable /\
 (forall k,k<>_j -> lef!k=le!k) /\ lframe (root_prefix_frame e ba) m mf.
Proof.
 intros Sep Owned Outside EQ EM HA BW W FW.
 destruct (exec_root_prefix e le m ba w Sep Owned Outside EQ EM HA BW W FW)
   as (mi & Prefix & OwnedI & StoreI & WI & FWI & FrameI).
 destruct (exec_root_chain_owned e le mi (root_initial_x2 w) (root_initial_x3 w) EQ EM Sep OwnedI StoreI)
   as (mf & lef & Chain & OwnedF & StoreF & Temps & FrameF).
 assert (WF : fe_at mf ba 0 (words5 w)).
 { eapply curve_keep_field_range;[reflexivity|exact WI|exact FrameF|];intros;exact Outside. }
 assert (FWF : Mem.range_perm mf ba 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FWI|exact FrameF|];intros;exact Outside. }
 exists mf,lef;split.
 - apply exec_statement_prefix_then_last with (le1:=le) (m1:=mi).
   + rewrite root_prefix_as_sequence;exact Prefix.
   + exact Chain.
 - split;[exact OwnedF|];split;[exact StoreF|];split;[exact WF|];split;[exact FWF|];split;[exact Temps|].
   eapply lframe_trans;[exact FrameI|].
   eapply lframe_implies;[exact FrameF|];intros b pos [HO _] _;exact HO.
Qed.
