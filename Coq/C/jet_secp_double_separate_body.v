(** Complete original distinct-source doubling body. The arithmetic is split
    only at the actual sequence spine; helper results are derived from the
    initial coordinates, permissions and disjoint private storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_double_statements C.jet_secp_double_flag
 C.jet_secp_double_separate_prefix C.jet_secp_double_separate_tail C.jet_secp_double_all_calls
 C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_statement_prefix
 C.jet_secp_local_regions C.jet_secp_point_write_run.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma double_separate_arithmetic_source : double_arithmetic_body=
 statement_sequence (firstn 5 (fst (split_statement_last double_arithmetic_body))) double_separate_tail.
Proof. reflexivity. Qed.

Theorem exec_double_separate_arithmetic le x y z m br ba bs bl bt :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 br<>ba -> br<>bs -> br<>bl -> br<>bt ->
 ba<>bs -> ba<>bl -> ba<>bt -> bs<>bl -> bs<>bt -> bl<>bt ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bl 0 40 Cur Freeable ->
 Mem.range_perm m bt 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge (double_helper_env bl bs bt) le m double_arithmetic_body E0 le mf Out_normal /\
 fe_at mf br 0 (words5 (double_output_x_words x y)) /\
 fe_at mf br 40 (words5 (double_output_y_words x y)) /\
 fe_at mf br 80 (words5 (double_output_z_words y z)) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bl 0 40 Cur Freeable /\
 Mem.range_perm mf bt 0 40 Cur Freeable /\
 square_input_bounds (double_output_x_words x y) /\
 square_input_bounds (double_output_y_words x y) /\
 square_input_bounds (double_output_z_words y z) /\
 lframe (double_separate_frame br ba bs bl bt) m mf.
Proof.
 intros HA HR BX BY BZ RA RS RL RT AS AL AT SL ST LT X Y ZAt RF AF SF LF TF.
 destruct (exec_double_separate_prefix le x y z m br ba bs bl bt HA HR BX BY BZ
   RA RS RL AS AL SL X Y ZAt RF AF SF LF)
  as (m5 & Prefix & RZ5 & X5 & Y5 & Z5 & S5 & L5 & RF5 & AF5 & SF5 & LF5 & BZ5 & BS5 & BL5 & F05).
 assert (TF5:Mem.range_perm m5 bt 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact TF|exact F05|].
   intros pos;repeat split;try congruence;left;congruence. }
 destruct (exec_double_separate_tail le x y z m5 br ba bs bl bt HA HR BX BS5 BL5 BZ5
   RA RS RL RT AS AL AT SL ST LT X5 Y5 Z5 RZ5 S5 L5 RF5 AF5 SF5 LF5 TF5)
  as (mf & Tail & RXF & RYF & RZF & AXF & AYF & AZF & RFF & AFF & SFF & LFF & TFF & BXF & BYF & BZF & Frame).
 exists mf;split.
 - rewrite double_separate_arithmetic_source;eapply exec_statement_prefix_then_last;
    [exact Prefix|exact Tail].
 - split;[exact RXF|];split;[exact RYF|];split;[exact RZF|];split;[exact AXF|];
   split;[exact AYF|];split;[exact AZF|];split;[exact RFF|];split;[exact AFF|];
   split;[exact SFF|];split;[exact LFF|];split;[exact TFF|];
   split;[exact BXF|];split;[exact BYF|];split;[exact BZF|].
   eapply lframe_trans;[|exact Frame].
   eapply lframe_implies;[exact F05|].
   intros b pos (NS & NL & NT & NR & NA) Valid;repeat split;try assumption.
   destruct NR as [NR|[NR|NR]];[left;exact NR|right;left;lia|right;right;exact NR].
Qed.

Definition double_separate_body_frame (br ba bs bl bt b:block) (pos:Z) :=
 b<>bs /\ b<>bl /\ b<>bt /\ (b<>br \/ pos<0 \/ 124<=pos) /\ (b<>ba \/ pos<0 \/ 120<=pos).

Lemma exec_double_separate_flag e le m mi br ba flag :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
 Mem.load Mint32 m ba 120=Some (Vint flag) -> Mem.store Mint32 m br 120 (Vint flag)=Some mi ->
 Clight2.exec_stmt secp_ge e le m double_flag_stmt E0 (PTree.set _t'1 (Vint flag) le) mi Out_normal.
Proof.
 intros HA HR Load Store;unfold double_flag_stmt.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'1 (Vint flag) le).
 - apply exec_Sset;eapply eval_Elvalue.
   + apply eval_double_flag_field;exact HA.
   + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact Load].
 - eapply exec_Sassign with (loc:=br) (ofs:=Ptrofs.repr 120) (bf:=Full) (v2:=Vint flag) (v:=Vint flag).
   + apply eval_double_flag_field;rewrite PTree.gso by discriminate;exact HR.
   + apply eval_Etempvar;apply PTree.gss.
   + reflexivity.
   + eapply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
Qed.

Theorem exec_double_separate_body le x y z m br ba bs bl bt flag :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 br<>ba -> br<>bs -> br<>bl -> br<>bt ->
 ba<>bs -> ba<>bl -> ba<>bt -> bs<>bl -> bs<>bt -> bl<>bt ->
 Mem.load Mint32 m ba 120=Some (Vint flag) ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bl 0 40 Cur Freeable ->
 Mem.range_perm m bt 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge (double_helper_env bl bs bt) le m (fn_body f_secp256k1_gej_double)
   E0 (PTree.set _t'1 (Vint flag) le) mf Out_normal /\
 fe_at mf br 0 (words5 (double_output_x_words x y)) /\
 fe_at mf br 40 (words5 (double_output_y_words x y)) /\
 fe_at mf br 80 (words5 (double_output_z_words y z)) /\
 Mem.load Mint32 mf br 120=Some (Vint flag) /\ Mem.load Mint32 mf ba 120=Some (Vint flag) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bl 0 40 Cur Freeable /\
 Mem.range_perm mf bt 0 40 Cur Freeable /\
 square_input_bounds (double_output_x_words x y) /\
 square_input_bounds (double_output_y_words x y) /\
 square_input_bounds (double_output_z_words y z) /\
 lframe (double_separate_body_frame br ba bs bl bt) m mf.
Proof.
 intros HA HR BX BY BZ RA RS RL RT AS AL AT SL ST LT Flag X Y ZAt RF AF SF LF TF.
 assert (Access:Mem.valid_access m Mint32 br 120 Writable).
 { split;[intros pos Range;apply (freeable_range_writable m br 0 128 RF);
     change (120<=pos<124) in Range;lia|exists 30;reflexivity]. }
 destruct (Mem.valid_access_store m Mint32 br 120 (Vint flag) Access) as (mi & Store).
 assert (FI:lframe (fun b pos=>b<>br \/ pos<120 \/ 124<=pos) m mi).
 { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
   intros pos Range;change (120<=pos<124) in Range;intros [Same|[Low|High]];[contradiction|lia|lia]. }
 assert (XI:fe_at mi ba 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FI|];intros;left;congruence).
 assert (YI:fe_at mi ba 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FI|];intros;left;congruence).
 assert (ZI:fe_at mi ba 80 (words5 z)) by (eapply field_at_lframe;[exact ZAt|exact FI|];intros;left;congruence).
 assert (RFI:Mem.range_perm mi br 0 128 Cur Freeable) by
   (intros pos Range;eapply Mem.perm_store_1;[exact Store|apply RF;exact Range]).
 assert (AFI:Mem.range_perm mi ba 0 128 Cur Freeable) by
   (eapply curve_keep_free;[lia|exact AF|exact FI|];intros;left;congruence).
 assert (SFI:Mem.range_perm mi bs 0 40 Cur Freeable) by
   (eapply curve_keep_free;[lia|exact SF|exact FI|];intros;left;congruence).
 assert (LFI:Mem.range_perm mi bl 0 40 Cur Freeable) by
   (eapply curve_keep_free;[lia|exact LF|exact FI|];intros;left;congruence).
 assert (TFI:Mem.range_perm mi bt 0 40 Cur Freeable) by
   (eapply curve_keep_free;[lia|exact TF|exact FI|];intros;left;congruence).
 assert (AI:Mem.load Mint32 mi ba 120=Some (Vint flag)) by
   (rewrite (Mem.load_store_other _ _ _ _ _ _ Store);[exact Flag|left;congruence]).
 assert (RI:Mem.load Mint32 mi br 120=Some (Vint flag)) by (exact (Mem.load_store_same _ _ _ _ _ _ Store)).
 set (li:=PTree.set _t'1 (Vint flag) le).
 destruct (exec_double_separate_arithmetic li x y z mi br ba bs bl bt
   ltac:(unfold li;rewrite PTree.gso by discriminate;exact HA)
   ltac:(unfold li;rewrite PTree.gso by discriminate;exact HR)
   BX BY BZ RA RS RL RT AS AL AT SL ST LT XI YI ZI RFI AFI SFI LFI TFI)
  as (mf & Arithmetic & RXF & RYF & RZF & AXF & AYF & AZF & RFF & AFF & SFF & LFF & TFF & BXF & BYF & BZF & Frame).
 assert (RV:Mem.valid_block mi br) by (eapply Mem.perm_valid_block;exact (RFI 0 ltac:(lia))).
 assert (AV:Mem.valid_block mi ba) by (eapply Mem.perm_valid_block;exact (AFI 0 ltac:(lia))).
 assert (FlagR:Mem.load Mint32 mf br 120=Some (Vint flag)).
 { rewrite (proj1 Frame Mint32 br 120 RV);[exact RI|].
   intros pos Range;change (120<=pos<124) in Range;unfold double_separate_frame;
     repeat split;try congruence;right;right;lia. }
 assert (FlagA:Mem.load Mint32 mf ba 120=Some (Vint flag)).
 { rewrite (proj1 Frame Mint32 ba 120 AV);[exact AI|].
   intros pos Range;change (120<=pos<124) in Range;unfold double_separate_frame;
     repeat split;try congruence;right;right;lia. }
 exists mf;split.
 - rewrite double_helper_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=li);
    [apply exec_double_separate_flag with (br:=br) (ba:=ba);assumption|exact Arithmetic].
 - split;[exact RXF|];split;[exact RYF|];split;[exact RZF|];split;[exact FlagR|];split;[exact FlagA|];
   split;[exact AXF|];split;[exact AYF|];split;[exact AZF|];split;[exact RFF|];split;[exact AFF|];
   split;[exact SFF|];split;[exact LFF|];split;[exact TFF|];
   split;[exact BXF|];split;[exact BYF|];split;[exact BZF|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact FI|].
     intros b pos (NS & NL & NT & NR & NA) Valid;destruct NR as [NR|[NR|NR]];intuition lia.
   + eapply lframe_implies;[exact Frame|].
     intros b pos (NS & NL & NT & NR & NA) Valid;unfold double_separate_frame;
       repeat split;try assumption;destruct NR as [NR|[NR|NR]];intuition lia.
Qed.
